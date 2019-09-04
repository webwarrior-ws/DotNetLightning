namespace DotNetLightning.Infrastructure


open System.IO.Pipelines
open System.Collections.Concurrent
open System.Threading.Tasks


open FSharp.Control.Tasks

open Microsoft.Extensions.Logging
open Microsoft.Extensions.Options

open NBitcoin
open DotNetLightning.Utils
open DotNetLightning.Chain
open DotNetLightning.Serialize.Msgs
open DotNetLightning.LN

open CustomEventAggregator
open DotNetLightning.Utils.Aether
open FSharp.Control.Reactive


type PeerError =
    | DuplicateConnection of PeerId
    | UnexpectedByteLength of expected: int * actual: int
    | EncryptorError of string

type IPeerManager =
    abstract member ProcessMessageAsync: PeerId * IDuplexPipe -> ValueTask
    abstract member AcceptCommand : PeerCommand -> ValueTask

type PeerManager(keyRepo: IKeysRepository,
                 logger: ILogger<PeerManager>,
                 nodeParams: IOptions<NodeParams>,
                 eventAggregator: IEventAggregator,
                 chainWatcher: IChainWatcher,
                 broadCaster: IBroadCaster) as this =
    let _logger = logger
    let _nodeParams = nodeParams.Value
    let ascii = System.Text.ASCIIEncoding.ASCII
    
    let _chainWatcher = chainWatcher
    let _broadCaster = broadCaster
    
    let _channelEventObservable =
        eventAggregator.GetObservable<NodeId * ChannelEvent>()
        |> Observable.flatmapAsync(this.ChannelEventListener)
        
    member val KnownPeers = ConcurrentDictionary<PeerId, Peer>() with get, set
    
    member val OpenedPeers = ConcurrentDictionary<PeerId, Peer>() with get, set
    member val PeerIdToTransport = ConcurrentDictionary<PeerId, PipeWriter>() with get

    member val NodeIdToDescriptor = ConcurrentDictionary<NodeId, PeerId>() with get, set
    
    member val EventAggregator: IEventAggregator = eventAggregator with get
    member private this.ChannelEventListener (nodeId, e): Async<unit> =
        let vt = vtask {
            let peerId = this.NodeIdToDescriptor.TryGet(nodeId)
            let transport = this.PeerIdToTransport.TryGet(peerId)
            match e with
            | ChannelEvent.WeAcceptedOpenChannel(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) msg
            | ChannelEvent.WeAcceptedFundingCreated(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) msg
            | ChannelEvent.NewOutboundChannelStarted(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedAcceptChannel(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedFundingSigned(finalizedFundingTx, _) ->
                match _broadCaster.BroadCastTransaction(finalizedFundingTx.Value) with
                | Ok _ ->
                    let spk1 = finalizedFundingTx.Value.Outputs.[0].ScriptPubKey
                    let spk2 = finalizedFundingTx.Value.Outputs.[1].ScriptPubKey
                    let txHash = finalizedFundingTx.Value.GetHash()
                    match ([spk1; spk2]
                          |> List.map(fun spk -> _chainWatcher.InstallWatchTx(txHash, spk))
                          |> List.forall(id)) with
                    | true ->
                        _logger.LogInformation(sprintf "Waiting for funding tx (%A) to get confirmed..." txHash )
                        return ()
                    | false ->
                        _logger.LogCritical(sprintf "Failed to install watching tx (%A)" txHash)
                        this.EventAggregator.Publish<PeerEvent>(FailedToBroadcastTransaction(nodeId, finalizedFundingTx.Value))
                        return ()
                | Result.Error str ->
                    str |> _logger.LogCritical
                    this.EventAggregator.Publish<PeerEvent>(FailedToBroadcastTransaction(nodeId, finalizedFundingTx.Value))
                    return ()
            // The one which includes `CMD` in its names is the one started by us.
            // So there are no need to think about routing, just send it to specified peer.
            | ChannelEvent.WeAcceptedCMDAddHTLC (msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedCMDFulfillHTLC (msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedCMDFailHTLC(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedCMDFailMalformedHTLC(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedCMDUpdateFee(msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
            | ChannelEvent.WeAcceptedCMDSign (msg, _) ->
                return! this.EncodeAndSendMsg(peerId, transport) (msg)
        }
        vt.AsTask() |> Async.AwaitTask
            
    member private this.RememberPeersTransport(peerId: PeerId, pipe: PipeWriter) =
        match this.PeerIdToTransport.TryAdd(peerId, pipe) with
        | true -> ()
        | false ->
            sprintf "failed to remember peerId(%A) 's Transport. This should never happen" peerId
            |> _logger.LogCritical
            ()

    /// Initiate Handshake with peer by sending noise act-one
    /// `ie` is required only for testing. BOLT specifies specific ephemeral key for handshake
    member this.NewOutBoundConnection (theirNodeId: NodeId,
                                       peerId: PeerId,
                                       pipeWriter: PipeWriter,
                                       ?ie: Key) = vtask {
        let act1, peerEncryptor =
            PeerChannelEncryptor.newOutBound(theirNodeId)
            |> fun pce -> if (ie.IsNone) then pce else (Optic.set PeerChannelEncryptor.OutBoundIE_ ie.Value pce)
            |> PeerChannelEncryptor.getActOne
        sprintf "Going to create outbound peer for %A" peerId
        |> _logger.LogTrace
        let newPeer = {
                            ChannelEncryptor = peerEncryptor
                            IsOutBound = true
                            TheirNodeId = None
                            TheirGlobalFeatures = None
                            TheirLocalFeatures = None
                            SyncStatus = InitSyncTracker.NoSyncRequested
                            PeerId = peerId
                            GetOurNodeSecret = keyRepo.GetNodeSecret
                      }
        match this.KnownPeers.TryAdd(peerId, newPeer) with
        | false ->
            return peerId
                   |> DuplicateConnection
                   |> Result.Error
        | true ->
            this.RememberPeersTransport(peerId, pipeWriter)
            // send act1
            let! _ = pipeWriter.WriteAsync(act1)
            let! _ = pipeWriter.FlushAsync()
            return Ok()
        }

    member this.NewInboundConnection(peerId: PeerId, actOne: byte[], pipeWriter: PipeWriter, ?ourEphemeral) = vtask {
        if (actOne.Length <> 50) then return (UnexpectedByteLength(50, actOne.Length) |> Result.Error) else
        let secret = keyRepo.GetNodeSecret()
        let peerEncryptor = PeerChannelEncryptor.newInBound(secret)
        let r =
            if (ourEphemeral.IsSome) then
                (PeerChannelEncryptor.processActOneWithEphemeralKey actOne secret ourEphemeral.Value peerEncryptor)
            else
                (PeerChannelEncryptor.processActOneWithKey actOne secret peerEncryptor)
        match r with
        | Bad b -> return (b.Describe() |> PeerError.EncryptorError |> Result.Error)
        | Good (actTwo, pce) ->
            let newPeer = {
                ChannelEncryptor = pce
                IsOutBound = false
                TheirNodeId = None
                TheirGlobalFeatures = None
                TheirLocalFeatures = None

                SyncStatus = InitSyncTracker.NoSyncRequested
                PeerId = peerId
                GetOurNodeSecret = keyRepo.GetNodeSecret
            }
            "new peer created"
            |> _logger.LogTrace
            match this.KnownPeers.TryAdd(peerId, newPeer) with
            | false ->
                "duplicate connection"
                |> _logger.LogTrace
                return peerId
                |> DuplicateConnection
                |> Result.Error
            | true ->
                "Going to Write act Two to newly created peer"
                |> _logger.LogTrace
                this.RememberPeersTransport(peerId, pipeWriter)
                let! _ = pipeWriter.WriteAsync(actTwo)
                let! _ = pipeWriter.FlushAsync()
                return Ok (newPeer)
        }

    member private this.UpdatePeerWith(peerId, newPeer: Peer) =
        ignore <| this.KnownPeers.AddOrUpdate(peerId, newPeer, (fun pId exisintgPeer -> newPeer))
        if newPeer.ChannelEncryptor.IsReadyForEncryption() then
            ignore <| this.OpenedPeers.AddOrUpdate(peerId, newPeer, fun pId existingPeer -> newPeer)

    member private this.EncodeAndSendMsg(theirPeerId: PeerId, pipeWriter: PipeWriter) (msg: ILightningMsg) =
        unitVtask {
            match this.OpenedPeers.TryGetValue(theirPeerId) with
            | true, peer ->
                sprintf "Encoding and sending message of type %A to %A "  msg (peer.TheirNodeId)
                |> _logger.LogTrace
                let msgEncrypted, newPCE =
                    peer.ChannelEncryptor |> PeerChannelEncryptor.encryptMessage (_logger.LogTrace) (msg.ToBytes())
                this.UpdatePeerWith(theirPeerId, { peer with ChannelEncryptor = newPCE })
                do! pipeWriter.WriteAsync(msgEncrypted)
                return ()
            | false, _ ->
                sprintf "peerId %A is not in opened peers" theirPeerId
                |> _logger.LogCritical
        }

    member private this.HandleSetupMsgAsync(peerId, msg: ISetupMsg, peer: Peer, pipe: IDuplexPipe) =
        vtask {
            match msg with
            | :? Init as init ->
                if (init.GlobalFeatures.RequiresUnknownBits()) then
                    _logger.LogInformation("Peer global features required unknown version bits")
                    return RResult.rbad(RBad.Object({ PeerHandleError.NoConnectionPossible = true }))
                else if (init.LocalFeatures.RequiresUnknownBits()) then
                    _logger.LogInformation("Peer local features required unknown version bits")
                    return RResult.rbad(RBad.Object({ PeerHandleError.NoConnectionPossible = true }))
                else if (peer.TheirGlobalFeatures.IsSome) then
                    return RResult.rbad(RBad.Object({ PeerHandleError.NoConnectionPossible = false }))
                else
                    sprintf "Received peer Init message: data_loss_protect: %s, initial_routing_sync: %s , upfront_shutdown_script: %s, unknown local flags: %s, unknown global flags %s" 
                        (if init.LocalFeatures.SupportsDataLossProect() then "supported" else "not supported")
                        (if init.LocalFeatures.InitialRoutingSync() then "supported" else "not supported")
                        (if init.LocalFeatures.SupportsUpfrontShutdownScript() then "supported" else "not supported")
                        (if init.LocalFeatures.SupportsUnknownBits() then "present" else "not present")
                        (if init.GlobalFeatures.SupportsUnknownBits() then "present" else "not present")
                        |> _logger.LogInformation
                    this.EventAggregator.Publish<PeerEvent>(ReceivedInit (peer.TheirNodeId.Value, init))
                    let peer =
                        let p =
                            if (init.LocalFeatures.InitialRoutingSync()) then
                                { peer with SyncStatus = InitSyncTracker.ChannelsSyncing (ChannelId.Zero) }
                            else
                                peer
                        { p with TheirGlobalFeatures = Some init.GlobalFeatures; TheirLocalFeatures = Some init.LocalFeatures }
                    this.UpdatePeerWith(peerId, peer)
                    if (not peer.IsOutBound) then
                        let lf = LocalFeatures.Flags([||]).SetInitialRoutingSync()
                        do! this.EncodeAndSendMsg(peer.PeerId, pipe.Output) ({ Init.GlobalFeatures = GlobalFeatures.Flags([||]); Init.LocalFeatures = lf })
                        return Good (None)
                    else
                        this.EventAggregator.Publish<PeerEvent>(Connected peer.TheirNodeId.Value)
                        return Good (None)
            | :? ErrorMessage as e ->
                let isDataPrintable = e.Data |> Array.exists(fun b -> b < 32uy || b > 126uy) |> not
                do
                    if isDataPrintable then
                        sprintf "Got error message from %A:%A" (peer.TheirNodeId.Value) (ascii.GetString(e.Data))
                        |> _logger.LogDebug
                    else
                        sprintf "Got error message from %A with non-ASCII error message" (peer.TheirNodeId.Value)
                        |> _logger.LogDebug
                if (e.ChannelId = WhichChannel.All) then
                    return
                        { PeerHandleError.NoConnectionPossible = true }
                        |> box
                        |> RBad.Object
                        |> RResult.rbad
                else
                    this.EventAggregator.Publish<PeerEvent>(ReceivedError(peer.TheirNodeId.Value, e))
                    return Good (Some peer)
            | :? Ping as ping ->
                this.EventAggregator.Publish<PeerEvent>(ReceivedPing (peer.TheirNodeId.Value, ping))
                sprintf "Received ping from %A" peer.TheirNodeId
                |> _logger.LogDebug
                if (ping.PongLen < 65532us) then
                    let pong = { Pong.BytesLen = ping.PongLen }
                    do! this.EncodeAndSendMsg(peer.PeerId, pipe.Output) (pong)
                    return Good(None)
                else
                    return Good(Some peer)
            | :? Pong as pong ->
                sprintf "Received pong from %A"  peer.TheirNodeId.Value |> _logger.LogDebug
                this.EventAggregator.Publish<PeerEvent>(ReceivedPong (peer.TheirNodeId.Value, pong))
                return Good (Some peer)
            | _ -> return failwithf "Unknown setup message %A This should never happen" msg
        }

    member inline private this.TryPotentialHandleError (peerId, transport: IDuplexPipe) (b: RBad) =
        unitTask {
            let handleObj (o: obj) = 
                unitVtask {
                    match o with
                    | :? HandleError as he ->
                        sprintf "Got Error when handling message"
                        |> _logger.LogTrace
                        match he.Action with
                        | Some(DisconnectPeer _) ->
                            sprintf "disconnecting peer because %A" he.Error
                            |> _logger.LogTrace
                        | Some(IgnoreError) ->
                            sprintf "ignoring the error because %A" he.Error
                            |> _logger.LogTrace
                        | Some(SendErrorMessage msg) ->
                            sprintf "sending error message because %A" he.Error
                            |> _logger.LogTrace
                            let! _ = this.EncodeAndSendMsg(peerId, transport.Output) msg
                            return ()
                        | None ->
                            sprintf "Got error when handling message, action not yet filled in %A" he.Error
                            |> _logger.LogDebug
                    | _ ->
                        _logger.LogCritical(sprintf "Unknown Error object %A" o)
                }
            let! _ =
                unitTask {
                    match b with
                    | RBad.Exception ex -> _logger.LogError(ex.StackTrace)
                    | RBad.Message msg -> _logger.LogError(msg) 
                    | RBad.DescribedObject (msg, obj) ->
                        _logger.LogError(msg)
                        do! handleObj obj
                    | RBad.Object obj ->
                        do! handleObj obj
                }
            return ()
        }

    member private this.InsertNodeId(nodeId: NodeId, peerId) =
        match this.NodeIdToDescriptor.TryAdd(nodeId, peerId) with
        | false ->
            _logger.LogDebug(sprintf "Got second connection with %A , closing." nodeId)
            RResult.rbad(RBad.Object { HandleError.Action = Some IgnoreError ; Error = sprintf "We already have connection with %A. nodeid: is %A" peerId nodeId })
        | true ->
            _logger.LogTrace(sprintf "Finished noise handshake for connection with %A" nodeId)
            Good ()

    member this.ProcessMessageAsync(peerId: PeerId, pipe: IDuplexPipe) =
        this.ProcessMessageAsync(peerId, pipe, Key())
        
    /// read from pipe, If the handshake is not completed. proceed with handshaking process
    /// automatically. If it has been completed. This patch to message handlers
    /// <param name="ourEphemeral"> Used only for test. usually ephemeral keys can be generated randomly </param>
    member this.ProcessMessageAsync(peerId: PeerId, pipe: IDuplexPipe, ourEphemeral: Key) =
        let errorHandler: RBad -> Task = this.TryPotentialHandleError(peerId, pipe)
        unitVtask {
            let! r = this.ReadAsyncCore(peerId, pipe, ourEphemeral)
            let r: RResult<_> =  r // compiler complains about type annotation without this
            do! r.RBadIterAsync(errorHandler)
            match r with
            | Good (Some peer) ->
                this.UpdatePeerWith(peerId, peer)
            | _ -> ()
            return ()
        }
        
    // I wanted to use a bind (>>=) as we do in Channel, but we had to prepare monad-transformer.
    // so instead decided to just use match expression.
    member private this.ReadAsyncCore(peerId: PeerId, pipe: IDuplexPipe, ourEphemeral) =
        vtask {
            match this.KnownPeers.TryGetValue(peerId) with
            | false, _ ->
                sprintf "Going to create new inbound peer against %A" (peerId)
                |>  _logger.LogTrace 
                let! actOne = pipe.Input.ReadExactAsync(50, true)
                "Read act 1 from peer"
                |> _logger.LogTrace 
                let! r = this.NewInboundConnection(peerId, actOne, pipe.Output, ourEphemeral)
                _logger.LogTrace (sprintf "result for creating new inbound peer is %A" r)
                match r with
                | Ok p -> return Good (Some p)
                | Result.Error e -> return (e |> box |> RBad.Object |> RResult.rbad)
            // This case might be unnecessary. Since probably there is no way these are both true
            // 1. We know the peer
            // 2. peer has not sent act1 yet.
            // TODO: Remove?
            | true, peer when peer.ChannelEncryptor.GetNoiseStep() = ActOne ->
                sprintf "Going to read from act one from peer %A" peerId
                |>  _logger.LogTrace 
                let! actOne = pipe.Input.ReadExactAsync(50)
                match peer.ChannelEncryptor |> PeerChannelEncryptor.processActOneWithKey actOne (keyRepo.GetNodeSecret()) with
                | Bad rbad -> return Bad rbad
                | Good (actTwo, nextPCE) ->
                    do! pipe.Output.WriteAsync(actTwo)
                    return Good (Some { peer with ChannelEncryptor = nextPCE })
            | true, peer when peer.ChannelEncryptor.GetNoiseStep() = ActTwo ->
                let! actTwo = pipe.Input.ReadExactAsync(50)
                match peer.ChannelEncryptor |> PeerChannelEncryptor.processActTwo(actTwo) (keyRepo.GetNodeSecret()) with
                | Bad rbad -> return Bad rbad
                | Good ((actThree, theirNodeId), newPCE) ->
                    do! pipe.Output.WriteAsync(actThree)
                    let newPeer = { peer with TheirNodeId = Some theirNodeId; ChannelEncryptor = newPCE }
                    // it is necessary to  update peer here for sending first init data by `EncodeAndSendMsg`
                    this.UpdatePeerWith(peerId, newPeer)
                    match this.InsertNodeId(theirNodeId, peerId) with
                    | Bad rbad -> return Bad rbad
                    | Good _ -> 
                        let localFeatures = 
                            let lf = (LocalFeatures.Flags [||])
                            if _nodeParams.RequireInitialRoutingSync then
                                lf.SetInitialRoutingSync()
                            else
                                lf
                        do!
                            this.EncodeAndSendMsg (peerId, pipe.Output)
                                ({ Init.GlobalFeatures = GlobalFeatures.Flags [||]; LocalFeatures = localFeatures })
                        return Good (None)
            | true, peer when peer.ChannelEncryptor.GetNoiseStep() = ActThree ->
                let! actThree = pipe.Input.ReadExactAsync(66)
                match peer.ChannelEncryptor |> PeerChannelEncryptor.processActThree actThree with
                | Bad rbad -> return Bad rbad
                | Good (theirNodeId, newPCE) ->
                    match this.InsertNodeId(theirNodeId, peerId) with
                    | Bad b -> return Bad b
                    | Good _ ->
                        this.EventAggregator.Publish<PeerEvent>(Connected theirNodeId)
                        return Good (Some { peer with ChannelEncryptor = newPCE; TheirNodeId = Some theirNodeId })
            | true, peer when peer.ChannelEncryptor.GetNoiseStep() = NoiseComplete ->
                let! lengthHeader = pipe.Input.ReadExactAsync(18)
                match peer.ChannelEncryptor |> PeerChannelEncryptor.decryptLengthHeader (_logger.LogTrace) lengthHeader with
                | Bad b -> return Bad b
                | Good (length, newPCE) -> 
                    let peer = { peer with ChannelEncryptor = newPCE }
                    let! cipherTextWithMAC = pipe.Input.ReadExactAsync(int length + 16)
                    match peer.ChannelEncryptor |> PeerChannelEncryptor.decryptMessage (_logger.LogTrace) cipherTextWithMAC with
                    | Bad b -> return Bad b
                    | Good (data, newPCE) ->
                        let peer = { peer with ChannelEncryptor = newPCE }
                        match LightningMsg.fromBytes data with
                        | Bad b -> return Bad b
                        | Good msg ->
                            sprintf "Decrypted msg %A from %A" msg peerId |> _logger.LogDebug
                            match msg with
                            | :? ISetupMsg as setupMsg ->
                                return! this.HandleSetupMsgAsync (peerId, setupMsg, peer, pipe)
                            | :? IRoutingMsg as routingMsg ->
                                this.EventAggregator.Publish<PeerEvent>(ReceivedRoutingMsg (peer.TheirNodeId.Value, routingMsg))
                                return Good (Some peer)
                            | :? IChannelMsg as channelMsg ->
                                this.EventAggregator.Publish<PeerEvent>(ReceivedChannelMsg (peer.TheirNodeId.Value, channelMsg))
                                return Good (Some peer)
                            | msg -> return failwithf "Unknown type of message (%A), this should never happen" msg
            | _ -> return failwith "unreachable"
        }
    member this.AcceptCommand(cmd: PeerCommand) = unitVtask {
        match cmd with
        | Connect (peerId, nodeId) ->
            let pw = this.PeerIdToTransport.TryGet(peerId)
            match! this.NewOutBoundConnection(nodeId, peerId, pw) with
            | Ok _ -> return ()
            | Result.Error e ->
                sprintf "Failed to create out bound to peer (%A) (%A)" peerId e |> _logger.LogError
                return ()
        | SendPing (peerId, ping) ->
            let pw = this.PeerIdToTransport.TryGet(peerId)
            do! this.EncodeAndSendMsg (peerId, pw) (ping)
            return ()
    }

        
    interface IPeerManager with
        member this.ProcessMessageAsync(peerId, pipe) = this.ProcessMessageAsync(peerId, pipe)
        member this.AcceptCommand(cmd) = this.AcceptCommand(cmd)