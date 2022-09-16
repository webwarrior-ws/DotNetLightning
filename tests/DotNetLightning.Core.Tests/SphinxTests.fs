module SphinxTests

open ResultUtils
open Expecto
open Expecto.Logging
open Expecto.Logging.Message
open NBitcoin
open DotNetLightning.Utils
open DotNetLightning.Utils.OnionError
open DotNetLightning.Serialization.Msgs
open DotNetLightning.Crypto
open DotNetLightning.Crypto.Sphinx

let hex = NBitcoin.DataEncoders.HexEncoder()

let sessionKey =
    "4141414141414141414141414141414141414141414141414141414141414141"
    |> hex.DecodeData
    |> fun h -> new Key(h)

let privKeys =
    [
        "4141414141414141414141414141414141414141414141414141414141414141"
        "4242424242424242424242424242424242424242424242424242424242424242"
        "4343434343434343434343434343434343434343434343434343434343434343"
        "4444444444444444444444444444444444444444444444444444444444444444"
        "4545454545454545454545454545454545454545454545454545454545454545"
    ]
    |> List.map(hex.DecodeData >> fun h -> new Key(h))

let pubKeys = privKeys |> List.map(fun k -> k.PubKey)

let expectedPubKeys =
    [
        "02eec7245d6b7d2ccb30380bfbe2a3648cd7a942653f5aa340edcea1f283686619"
        "0324653eac434488002cc06bbfb7f10fe18991e35f9fe4302dbea6d2353dc0ab1c"
        "027f31ebc5462c1fdce1b737ecff52d37d75dea43ce11c74d25aa297165faa2007"
        "032c0b7cf95324a07d05398b240174dc0c2be444d96b159aa6c7f7b1e668680991"
        "02edabbd16b41c8371b92ef2f04c1185b4f03b6dcd52ba9b78d9d7c89c8f221145"
    ]
    |> List.map(hex.DecodeData >> PubKey)

let payloads =
    [
        "000000000000000000000000000000000000000000000000000000000000000000"
        "140101010101010101000000000000000100000001"
        "fd0100000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"
        "140303030303030303000000000000000300000003"
        "000404040404040404000000000000000400000004000000000000000000000000"
    ]
    |> List.map(hex.DecodeData)

let associatedData =
    "4242424242424242424242424242424242424242424242424242424242424242"
    |> hex.DecodeData

let logger = Log.create "Sphinx tests"
let logCore = eventX >> logger.info

let log _level =
    logCore

[<Tests>]
let bolt4Tests1 =
    testList
        "bolt4 tests (legacy hop_data)"
        [
            testCase "pubkey is as expected"
            <| fun _ -> Expect.equal (pubKeys) (expectedPubKeys) ""

            testCase "generate ephemeral keys and secrets"
            <| fun _ ->
                let (ephKeys, sharedSecrets) =
                    computeEphemeralPublicKeysAndSharedSecrets
                        sessionKey
                        pubKeys

                let expectedEphKeys =
                    [
                        "02eec7245d6b7d2ccb30380bfbe2a3648cd7a942653f5aa340edcea1f283686619"
                        "028f9438bfbf7feac2e108d677e3a82da596be706cc1cf342b75c7b7e22bf4e6e2"
                        "03bfd8225241ea71cd0843db7709f4c222f62ff2d4516fd38b39914ab6b83e0da0"
                        "031dde6926381289671300239ea8e57ffaf9bebd05b9a5b95beaf07af05cd43595"
                        "03a214ebd875aab6ddfd77f22c5e7311d7f77f17a169e599f157bbcdae8bf071f4"
                    ]
                    |> List.map(hex.DecodeData >> PubKey)

                let expectedSharedSecrets =
                    [
                        "53eb63ea8a3fec3b3cd433b85cd62a4b145e1dda09391b348c4e1cd36a03ea66"
                        "a6519e98832a0b179f62123b3567c106db99ee37bef036e783263602f3488fae"
                        "3a6b412548762f0dbccce5c7ae7bb8147d1caf9b5471c34120b30bc9c04891cc"
                        "21e13c2d7cfe7e18836df50872466117a295783ab8aab0e7ecc8c725503ad02d"
                        "b5756b9b542727dbafc6765a49488b023a725d631af688fc031217e90770c328"
                    ]
                    |> List.map(hex.DecodeData >> fun h -> new Key(h))

                Expect.equal ephKeys expectedEphKeys ""
                Expect.equal sharedSecrets expectedSharedSecrets ""

            testCase "generate filler"
            <| fun _ ->
                let (_, sharedSecrets) =
                    computeEphemeralPublicKeysAndSharedSecrets
                        sessionKey
                        pubKeys

                let filler =
                    generateFiller
                        "rho"
                        (payloads |> List.take(payloads.Length - 1))
                        (sharedSecrets |> List.take(sharedSecrets.Length - 1))

                let expectedFiller =
                    "b77d99c935d3f32469844f7e09340a91ded147557bdd0456c369f7e449587c0f5666faab58040146db49024db88553729bce12b860391c29c1779f022ae48a9cb314ca35d73fc91addc92632bcf7ba6fd9f38e6fd30fabcedbd5407b6648073c38331ee7ab0332f41f550c180e1601f8c25809ed75b3a1e78635a2ef1b828e92c9658e76e49f995d72cf9781eec0c838901d0bdde3ac21c13b4979ac9e738a1c4d0b9741d58e777ad1aed01263ad1390d36a18a6b92f4f799dcf75edbb43b7515e8d72cb4f827a9af0e7b9338d07b1a24e0305b5535f5b851b1144bad6238b9d9482b5ba6413f1aafac3cdde5067966ed8b78f7c1c5f916a05f874d5f17a2b7d0ae75d66a5f1bb6ff932570dc5a0cf3ce04eb5d26bc55c2057af1f8326e20a7d6f0ae644f09d00fac80de60f20aceee85be41a074d3e1dda017db79d0070b99f54736396f206ee3777abd4c00a4bb95c871750409261e3b01e59a3793a9c20159aae4988c68397a1443be6370fd9614e46108291e615691729faea58537209fa668a172d066d0efff9bc77c2bd34bd77870ad79effd80140990e36731a0b72092f8d5bc8cd346762e93b2bf203d00264e4bc136fc142de8f7b69154deb05854ea88e2d7506222c95ba1aab065c8a"
                    |> hex.DecodeData

                Expect.equal filler expectedFiller ""

            testCase "Create packet (reference test vector)"
            <| fun _ ->
                let (onion, _ss) =
                    let p =
                        PacketAndSecrets.Create(
                            sessionKey,
                            pubKeys,
                            payloads,
                            associatedData,
                            PacketFiller.DeterministicPacketFiller
                        )

                    (p.Packet, p.SharedSecrets)

                let expectedPacket =
                    "0002eec7245d6b7d2ccb30380bfbe2a3648cd7a942653f5aa340edcea1f283686619e5f14350c2a76fc232b5e46d421e9615471ab9e0bc887beff8c95fdb878f7b3a710f8eaf9ccc768f66bb5dec1f7827f33c43fe2ddd05614c8283aa78e9e7573f87c50f7d61ab590531cf08000178a333a347f8b4072e1cea42da7552402b10765adae3f581408f35ff0a71a34b78b1d8ecae77df96c6404bae9a8e8d7178977d7094a1ae549f89338c0777551f874159eb42d3a59fb9285ad4e24883f27de23942ec966611e99bee1cee503455be9e8e642cef6cef7b9864130f692283f8a973d47a8f1c1726b6e59969385975c766e35737c8d76388b64f748ee7943ffb0e2ee45c57a1abc40762ae598723d21bd184e2b338f68ebff47219357bd19cd7e01e2337b806ef4d717888e129e59cd3dc31e6201ccb2fd6d7499836f37a993262468bcb3a4dcd03a22818aca49c6b7b9b8e9e870045631d8e039b066ff86e0d1b7291f71cefa7264c70404a8e538b566c17ccc5feab231401e6c08a01bd5edfc1aa8e3e533b96e82d1f91118d508924b923531929aea889fcdf057f5995d9731c4bf796fb0e41c885d488dcbc68eb742e27f44310b276edc6f652658149e7e9ced4edde5d38c9b8f92e16f6b4ab13d710ee5c193921909bdd75db331cd9d7581a39fca50814ed8d9d402b86e7f8f6ac2f3bca8e6fe47eb45fbdd3be21a8a8d200797eae3c9a0497132f92410d804977408494dff49dd3d8bce248e0b74fd9e6f0f7102c25ddfa02bd9ad9f746abbfa3379834bc2380d58e9d23237821475a1874484783a15d68f47d3dc339f38d9bf925655d5c946778680fd6d1f062f84128895aff09d35d6c92cca63d3f95a9ee8f2a84f383b4d6a087533e65de12fc8dcaf85777736a2088ff4b22462265028695b37e70963c10df8ef2458756c73007dc3e544340927f9e9f5ea4816a9fd9832c311d122e9512739a6b4714bba590e31caa143ce83cb84b36c738c60c3190ff70cd9ac286a9fd2ab619399b68f1f7447be376ce884b5913c8496d01cbf7a44a60b6e6747513f69dc538f340bc1388e0fde5d0c1db50a4dcb9cc0576e0e2474e4853af9623212578d502757ffb2e0e749695ed70f61c116560d0d4154b64dcf3cbf3c91d89fb6dd004dc19588e3479fcc63c394a4f9e8a3b8b961fce8a532304f1337f1a697a1bb14b94d2953f39b73b6a3125d24f27fcd4f60437881185370bde68a5454d816e7a70d4cea582effab9a4f1b730437e35f7a5c4b769c7b72f0346887c1e63576b2f1e2b3706142586883f8cf3a23595cc8e35a52ad290afd8d2f8bcd5b4c1b891583a4159af7110ecde092079209c6ec46d2bda60b04c519bb8bc6dffb5c87f310814ef2f3003671b3c90ddf5d0173a70504c2280d31f17c061f4bb12a978122c8a2a618bb7d1edcf14f84bf0fa181798b826a254fca8b6d7c81e0beb01bd77f6461be3c8647301d02b04753b0771105986aa0cbc13f7718d64e1b3437e8eef1d319359914a7932548c91570ef3ea741083ca5be5ff43c6d9444d29df06f76ec3dc936e3d180f4b6d0fbc495487c7d44d7c8fe4a70d5ff1461d0d9593f3f898c919c363fa18341ce9dae54f898ccf3fe792136682272941563387263c51b2a2f32363b804672cc158c9230472b554090a661aa81525d11876eefdcc45442249e61e07284592f1606491de5c0324d3af4be035d7ede75b957e879e9770cdde2e1bbc1ef75d45fe555f1ff6ac296a2f648eeee59c7c08260226ea333c285bcf37a9bbfa57ba2ab8083c4be6fc2ebe279537d22da96a07392908cf22b233337a74fe5c603b51712b43c3ee55010ee3d44dd9ba82bba3145ec358f863e04bbfa53799a7a9216718fd5859da2f0deb77b8e315ad6868fdec9400f45a48e6dc8ddbaeb3"
                    |> hex.DecodeData

                CheckArrayEqual (onion.ToBytes()) (expectedPacket)

                let {
                        Payload = payload0
                        NextPacket = nextPacket0
                        SharedSecret = _ss0
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[0])
                        (associatedData)
                        (onion.ToBytes())
                    |> fun rr ->
                        Expect.isOk (Result.ToFSharpCoreResult rr) ""
                        Result.defaultWith (fun _ -> failwith "Unreachable") rr

                let {
                        Payload = payload1
                        NextPacket = nextPacket1
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[1])
                        (associatedData)
                        (nextPacket0.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 create packet ref test vector defaultClosure1"
                    )

                let {
                        Payload = payload2
                        NextPacket = nextPacket2
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[2])
                        (associatedData)
                        (nextPacket1.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 create packet ref test vector defaultClosure2"
                    )

                let {
                        Payload = payload3
                        NextPacket = nextPacket3
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[3])
                        (associatedData)
                        (nextPacket2.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 create packet ref test vector defaultClosure3"
                    )

                let {
                        Payload = payload4
                        NextPacket = nextPacket4
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[4])
                        (associatedData)
                        (nextPacket3.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 create packet ref test vector defaultClosure1"
                    )

                Expect.equal
                    [
                        payload0
                        payload1
                        payload2
                        payload3
                        payload4
                    ]
                    payloads
                    ""

                Expect.equal
                    nextPacket0.HMAC
                    ("4ecb91c341543953a34d424b64c36a9cd8b4b04285b0c8de0acab0b6218697fc"
                     |> hex.DecodeData
                     |> uint256)
                    ""

                Expect.equal
                    nextPacket1.HMAC
                    ("3d8e429a1e8d7bdb2813cd491f17771aa75670d88b299db1954aa015d035408f"
                     |> hex.DecodeData
                     |> uint256)
                    ""

                Expect.equal
                    nextPacket2.HMAC
                    ("30ad58843d142609ed7ae2b960c8ce0e331f7d45c7d705f67fd3f3978cd7b8f8"
                     |> hex.DecodeData
                     |> uint256)
                    ""

                Expect.equal
                    nextPacket3.HMAC
                    ("4ee0600ee609f1f3356b85b0af8ead34c2db4ae93e3978d15f983040e8b01acd"
                     |> hex.DecodeData
                     |> uint256)
                    ""

                Expect.equal
                    nextPacket4.HMAC
                    ("0000000000000000000000000000000000000000000000000000000000000000"
                     |> hex.DecodeData
                     |> uint256)
                    ""

                ()

            testCase "last node replies with an error message"
            <| fun _ ->
                let (onion, ss) =
                    let p =
                        PacketAndSecrets.Create(
                            sessionKey,
                            pubKeys,
                            payloads,
                            associatedData,
                            PacketFiller.BlankPacketFiller
                        )

                    (p.Packet, p.SharedSecrets)

                let {
                        NextPacket = packet1
                        SharedSecret = ss0
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[0])
                        (associatedData)
                        (onion.ToBytes())
                    |> fun r ->
                        Expect.isOk (Result.ToFSharpCoreResult r) ""

                        Result.defaultWith
                            (fun _ ->
                                failwith
                                    "Fail: bolt4 last node replies with err msg defaultClosure0"
                            )
                            r

                let {
                        NextPacket = packet2
                        SharedSecret = ss1
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[1])
                        (associatedData)
                        (packet1.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 last node replies with err msg defaultClosure1"
                    )

                let {
                        NextPacket = packet3
                        SharedSecret = ss2
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[2])
                        (associatedData)
                        (packet2.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 last node replies with err msg defaultClosure2"
                    )

                let {
                        NextPacket = packet4
                        SharedSecret = ss3
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[3])
                        (associatedData)
                        (packet3.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 last node replies with err msg defaultClosure3"
                    )

                let {
                        NextPacket = packet5
                        SharedSecret = ss4
                    }: ParsedPacket =
                    Sphinx.parsePacket
                        (privKeys.[4])
                        (associatedData)
                        (packet4.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 last node replies with err msg defaultClosure4"
                    )

                Expect.isTrue (packet5.IsLastPacket) ""

                let error =
                    ErrorPacket.Create(
                        ss4,
                        {
                            FailureMsg.Code =
                                FailureCode(OnionError.TEMPORARY_NODE_FAILURE)
                            Data = TemporaryNodeFailure
                        }
                    )

                let expected =
                    "a5e6bd0c74cb347f10cce367f949098f2457d14c046fd8a22cb96efb30b0fdcda8cb9168b50f2fd45edd73c1b0c8b33002df376801ff58aaa94000bf8a86f92620f343baef38a580102395ae3abf9128d1047a0736ff9b83d456740ebbb4aeb3aa9737f18fb4afb4aa074fb26c4d702f42968888550a3bded8c05247e045b866baef0499f079fdaeef6538f31d44deafffdfd3afa2fb4ca9082b8f1c465371a9894dd8c243fb4847e004f5256b3e90e2edde4c9fb3082ddfe4d1e734cacd96ef0706bf63c9984e22dc98851bcccd1c3494351feb458c9c6af41c0044bea3c47552b1d992ae542b17a2d0bba1a096c78d169034ecb55b6e3a7263c26017f033031228833c1daefc0dedb8cf7c3e37c9c37ebfe42f3225c326e8bcfd338804c145b16e34e4"
                    |> hex.DecodeData

                Expect.equal (expected) error ""

                let error1 = Sphinx.forwardErrorPacket(error, ss3)

                let expected =
                    "c49a1ce81680f78f5f2000cda36268de34a3f0a0662f55b4e837c83a8773c22aa081bab1616a0011585323930fa5b9fae0c85770a2279ff59ec427ad1bbff9001c0cd1497004bd2a0f68b50704cf6d6a4bf3c8b6a0833399a24b3456961ba00736785112594f65b6b2d44d9f5ea4e49b5e1ec2af978cbe31c67114440ac51a62081df0ed46d4a3df295da0b0fe25c0115019f03f15ec86fabb4c852f83449e812f141a9395b3f70b766ebbd4ec2fae2b6955bd8f32684c15abfe8fd3a6261e52650e8807a92158d9f1463261a925e4bfba44bd20b166d532f0017185c3a6ac7957adefe45559e3072c8dc35abeba835a8cb01a71a15c736911126f27d46a36168ca5ef7dccd4e2886212602b181463e0dd30185c96348f9743a02aca8ec27c0b90dca270"
                    |> hex.DecodeData

                Expect.equal expected error1 ""

                let error2 = Sphinx.forwardErrorPacket(error1, ss2)

                let expected =
                    "a5d3e8634cfe78b2307d87c6d90be6fe7855b4f2cc9b1dfb19e92e4b79103f61ff9ac25f412ddfb7466e74f81b3e545563cdd8f5524dae873de61d7bdfccd496af2584930d2b566b4f8d3881f8c043df92224f38cf094cfc09d92655989531524593ec6d6caec1863bdfaa79229b5020acc034cd6deeea1021c50586947b9b8e6faa83b81fbfa6133c0af5d6b07c017f7158fa94f0d206baf12dda6b68f785b773b360fd0497e16cc402d779c8d48d0fa6315536ef0660f3f4e1865f5b38ea49c7da4fd959de4e83ff3ab686f059a45c65ba2af4a6a79166aa0f496bf04d06987b6d2ea205bdb0d347718b9aeff5b61dfff344993a275b79717cd815b6ad4c0beb568c4ac9c36ff1c315ec1119a1993c4b61e6eaa0375e0aaf738ac691abd3263bf937e3"
                    |> hex.DecodeData

                Expect.equal expected error2 ""

                let error3 = Sphinx.forwardErrorPacket(error2, ss1)

                let expected =
                    "aac3200c4968f56b21f53e5e374e3a2383ad2b1b6501bbcc45abc31e59b26881b7dfadbb56ec8dae8857add94e6702fb4c3a4de22e2e669e1ed926b04447fc73034bb730f4932acd62727b75348a648a1128744657ca6a4e713b9b646c3ca66cac02cdab44dd3439890ef3aaf61708714f7375349b8da541b2548d452d84de7084bb95b3ac2345201d624d31f4d52078aa0fa05a88b4e20202bd2b86ac5b52919ea305a8949de95e935eed0319cf3cf19ebea61d76ba92532497fcdc9411d06bcd4275094d0a4a3c5d3a945e43305a5a9256e333e1f64dbca5fcd4e03a39b9012d197506e06f29339dfee3331995b21615337ae060233d39befea925cc262873e0530408e6990f1cbd233a150ef7b004ff6166c70c68d9f8c853c1abca640b8660db2921"
                    |> hex.DecodeData

                Expect.equal expected error3 ""

                let error4 = Sphinx.forwardErrorPacket(error3, ss0)

                let expected =
                    "9c5add3963fc7f6ed7f148623c84134b5647e1306419dbe2174e523fa9e2fbed3a06a19f899145610741c83ad40b7712aefaddec8c6baf7325d92ea4ca4d1df8bce517f7e54554608bf2bd8071a4f52a7a2f7ffbb1413edad81eeea5785aa9d990f2865dc23b4bc3c301a94eec4eabebca66be5cf638f693ec256aec514620cc28ee4a94bd9565bc4d4962b9d3641d4278fb319ed2b84de5b665f307a2db0f7fbb757366067d88c50f7e829138fde4f78d39b5b5802f1b92a8a820865af5cc79f9f30bc3f461c66af95d13e5e1f0381c184572a91dee1c849048a647a1158cf884064deddbf1b0b88dfe2f791428d0ba0f6fb2f04e14081f69165ae66d9297c118f0907705c9c4954a199bae0bb96fad763d690e7daa6cfda59ba7f2c8d11448b604d12d"
                    |> hex.DecodeData

                Expect.equal expected error4 ""

                let {
                        OriginNode = pubkey
                        FailureMsg = failure
                    } =
                    ErrorPacket.TryParse(error4, ss)
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 last node replies with err msg defaultClosure end"
                    )

                Expect.equal (pubKeys.[4]) (pubkey.Value) ""
                Expect.equal (TemporaryNodeFailure) (failure.Data) ""
                ()

            testCase "Intermediate node replies with an error message"
            <| fun _ ->
                let {
                        Packet = packet
                        SharedSecrets = ss
                    } =
                    Sphinx.PacketAndSecrets.Create(
                        sessionKey,
                        pubKeys,
                        payloads,
                        associatedData,
                        PacketFiller.BlankPacketFiller
                    )

                let {
                        NextPacket = packet1
                        SharedSecret = ss0
                    } =
                    Sphinx.parsePacket
                        (privKeys.[0])
                        (associatedData)
                        (packet.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 intrm node replies with err msg defaultClosure0"
                    )

                let {
                        NextPacket = packet2
                        SharedSecret = ss1
                    } =
                    Sphinx.parsePacket
                        (privKeys.[1])
                        (associatedData)
                        (packet1.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 intrm node replies with err msg defaultClosure1"
                    )

                let {
                        SharedSecret = ss2
                    } =
                    Sphinx.parsePacket
                        (privKeys.[2])
                        (associatedData)
                        (packet2.ToBytes())
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 intrm node replies with err msg defaultClosure2"
                    )

                let error =
                    ErrorPacket.Create(
                        ss2,
                        {
                            Code = OnionError.FailureCode INVALID_REALM
                            Data = InvalidRealm
                        }
                    )

                let error1 = forwardErrorPacket(error, ss1)
                let error2 = forwardErrorPacket(error1, ss0)

                let {
                        OriginNode = pubkey
                        FailureMsg = failure
                    } =
                    ErrorPacket.TryParse(error2, ss)
                    |> Result.defaultWith(fun _ ->
                        failwith
                            "Fail: bolt4 intrm node replies with err msg defaultClosure end"
                    )

                Expect.equal (pubkey.Value) (pubKeys.[2]) ""
                Expect.equal (InvalidRealm) (failure.Data) ""
                ()
        ]
