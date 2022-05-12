[<AutoOpen>]
module DotNetLightning.ClnRpc.Tests.Helpers

open System.Collections.Generic
open System.IO
open System.IO.Pipelines
open System.Text
open System.Text.Json
open DotNetLightning.ClnRpc.Plugin
open DotNetLightning.Serialization


let utf8 = UTF8Encoding.UTF8

let inline flatten(s: string) =
    s |> JsonSerializer.Deserialize<JsonDocument> |> JsonSerializer.Serialize

let initStr =
    $"""
  {{
    "id": 0,
    "method": "init",
    "jsonrpc": "2.0",
    "params": {{
      "options": {{
        "greeting": "World",
        "number": [0]
      }},
      "configuration": {{
        "lightning-dir": "/home/user/.lightning/testnet",
        "rpc-file": "lightning-rpc",
        "startup": true,
        "network": "testnet",
        "feature_set": {{
            "init": "02aaa2",
            "node": "8000000002aaa2",
            "channel": "",
            "invoice": "028200"
        }},
        "proxy": {{
            "type": "ipv4",
            "address": "127.0.0.1",
            "port": 9050
        }},
        "torv3-enabled": true,
        "always_use_proxy": false
      }}
    }}
  }}
  """

let initB = initStr |> flatten |> utf8.GetBytes

let initConfigDTO =
    {
        LightningInitConfigurationDTO.Network = "testnet"
        LightningDir = "/path/to/lightning_dir"
        RpcFile = "lightning-rpc"
        Startup = true
        FeatureSet =
            {
                FeatureSetDTO.Channel = None
                Init = None
                Node = "02aaa2" |> FeatureBits.ParseHexUnsafe |> Some
                Invoice = "02aaa2" |> FeatureBits.ParseHexUnsafe |> Some
            }
        Proxy =
            {
                ProxyDTO.Address = "localhost"
                Ty = "ipv4"
                Port = 1000
            }
        TorV3Enabled = true
        AlwaysUseProxy = false
    }

let initOptionsDTO = Dictionary<string, obj>()

let initDTO =
    {
        Configuration = initConfigDTO
        Options = initOptionsDTO
    }

let newlineB = "\n\n" |> utf8.GetBytes

let setupRawStream<'T when 'T :> PluginServerBase>
    (
        p: 'T,
        msgs: byte [] seq,
        ct
    ) =
    task {
        let outStream =
            let outS = new MemoryStream()

            PipeWriter
                .Create(outS, StreamPipeWriterOptions(leaveOpen = true))
                .AsStream()

        let buf =
            Array.concat
                [
                    for m in msgs do
                        yield! [ m; newlineB ]
                ]

        let inStream =
            let inMemStream = new MemoryStream(buf)

            PipeReader
                .Create(inMemStream, StreamPipeReaderOptions(leaveOpen = true))
                .AsStream()

        let! _listener = p.StartAsync(outStream, inStream, ct)
        inStream.Flush()
        return p
    }
