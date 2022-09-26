module RouteCalculationTests

open NBitcoin
open NBitcoin.DataEncoders
open Expecto

open DotNetLightning.Utils
open DotNetLightning.Serialization.Msgs
open DotNetLightning.Routing

open DotNetLightning.Payment
open DotNetLightning.Serialization
open Generators

open ResultUtils
open ResultUtils.Portability

let hex = Encoders.Hex

[<AutoOpen>]
module Constants =
    let DEFAULT_AMOUNT_MSAT = LNMoney.MilliSatoshis 10000000L
    let DEFAULT_HTLC_MAXIMUM_MSAT = LNMoney.Satoshis 100000

let fsCheckConfig =
    { FsCheckConfig.defaultConfig with
        arbitrary = [ typeof<PrimitiveGenerators> ]
        maxTest = 2
    }

let makeChannelAnnCore(shortChannelId: ShortChannelId, nodeIdA, nodeIdB) =
    let isNode1(localNodeId: NodeId, remoteNodeId: NodeId) =
        localNodeId > remoteNodeId

    let (nodeId1, nodeId2) =
        if isNode1(nodeIdA, nodeIdB) then
            nodeIdA, nodeIdB
        else
            (nodeIdB, nodeIdA)

    {
        UnsignedChannelAnnouncementMsg.ShortChannelId = shortChannelId
        NodeId1 = nodeId1
        NodeId2 = nodeId2
        BitcoinKey1 = ((new Key()).PubKey |> ComparablePubKey)
        BitcoinKey2 = ((new Key()).PubKey |> ComparablePubKey)
        ChainHash = Network.RegTest.GenesisHash
        Features = FeatureBits.Zero
        ExcessData = [||]
    }

let makeChannelAnn(shortChannelId: uint64, nodeIdA: NodeId, nodeIdB: NodeId) =
    makeChannelAnnCore(
        ShortChannelId.FromUInt64(shortChannelId),
        nodeIdA,
        nodeIdB
    )

let pks =
    [
        "02999fa724ec3c244e4da52b4a91ad421dc96c9a810587849cd4b2469313519c73" //a
        "03f1cb1af20fe9ccda3ea128e27d7c39ee27375c8480f11a87c17197e97541ca6a" //b
        "0358e32d245ff5f5a3eb14c78c6f69c67cea7846bdf9aeeb7199e8f6fbb0306484" //c
        "029e059b6780f155f38e83601969919aae631ddf6faed58fe860c72225eb327d7c" //d
        "02f38f4e37142cc05df44683a83e22dea608cf4691492829ff4cf99888c5ec2d3a" //e
        "03fc5b91ce2d857f146fd9b986363374ffe04dc143d8bcd6d7664c8873c463cdfc" //f
        "03864ef025fde8fb587d989186ce6a4a186895ee44a926bfc370e2c366597a3f8f" //g
    ]
    |> List.map(hex.DecodeData >> PubKey >> NodeId)

let a, b, c, d, e, f, g =
    pks.[0], pks.[1], pks.[2], pks.[3], pks.[4], pks.[5], pks.[6]

let hops2Ids(route: seq<RoutingGraphEdge>) =
    route
    |> Seq.map(fun hop ->
        hop.ShortChannelId.ToBytes()
        |> fun x -> NBitcoin.Utils.ToUInt64(x, false)
    )

let hops2Nodes(route: seq<RoutingGraphEdge>) =
    route |> Seq.map(fun hop -> (hop.Target, hop.Source))

let makeUpdateCore
    (
        shortChannelId: ShortChannelId,
        nodeid1: NodeId,
        nodeid2: NodeId,
        feeBase: LNMoney,
        feeProportionalMillions: uint32,
        minHtlc: option<LNMoney>,
        maxHtlc: option<LNMoney>,
        cltvDelta: option<BlockHeightOffset16>
    ) : (ChannelDesc * UnsignedChannelUpdateMsg) =
    let minHtlc = Option.defaultValue Constants.DEFAULT_AMOUNT_MSAT minHtlc
    let cltvDelta = Option.defaultValue (BlockHeightOffset16(0us)) cltvDelta

    let desc =
        {
            ChannelDesc.ShortChannelId = shortChannelId
            A = nodeid1
            B = nodeid2
        }

    let update =
        {
            UnsignedChannelUpdateMsg.MessageFlags =
                match maxHtlc with
                | Some _ -> 1uy
                | _ -> 0uy
            ChannelFlags = 0uy
            ChainHash = Network.RegTest.GenesisHash
            ShortChannelId = shortChannelId
            Timestamp = 0u
            CLTVExpiryDelta = cltvDelta
            HTLCMinimumMSat = minHtlc
            FeeBaseMSat = feeBase
            FeeProportionalMillionths = feeProportionalMillions
            // htlc_maximum_msat must always be present
            HTLCMaximumMSat =
                Some(maxHtlc |> Option.defaultValue DEFAULT_HTLC_MAXIMUM_MSAT)
        }

    desc, update

let makeUpdate
    (
        shortChannelId: uint64,
        nodeid1: NodeId,
        nodeid2: NodeId,
        feeBase: LNMoney,
        feeProportionalMillions: uint32,
        minHtlc: option<LNMoney>,
        maxHtlc: option<LNMoney>,
        cltvDelta: option<BlockHeightOffset16>
    ) : (ChannelDesc * UnsignedChannelUpdateMsg) =
    makeUpdateCore(
        shortChannelId |> ShortChannelId.FromUInt64,
        nodeid1,
        nodeid2,
        feeBase,
        feeProportionalMillions,
        minHtlc,
        maxHtlc,
        cltvDelta
    )

let makeUpdateSimple(shortChannelId, a, b) =
    makeUpdate(shortChannelId, a, b, LNMoney.Zero, 0u, None, None, None)

let makeUpdatesMap(updateMsgs: seq<UnsignedChannelUpdateMsg>) =
    let mutable updatesMap: Map<ShortChannelId, ChannelUpdates> = Map.empty

    for updMsg in updateMsgs do
        let oldValue =
            match updatesMap |> Map.tryFind updMsg.ShortChannelId with
            | Some(updates) -> updates
            | None -> ChannelUpdates.Empty

        updatesMap <-
            updatesMap |> Map.add updMsg.ShortChannelId (oldValue.With updMsg)

    updatesMap

let totalRouteCost (amount: LNMoney) (route: seq<RoutingGraphEdge>) =
    route
    |> Seq.toArray
    |> Array.rev
    |> Array.skipBack 1
    |> Array.fold
        (fun acc edge -> acc + EdgeWeightCaluculation.edgeFeeCost acc edge)
        amount


[<Tests>]
let tests =
    testList
        "Route Calculation"
        [
            let calculateRouteSimple() =
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(1L),
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(1L),
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(1L),
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(1L),
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                    ]
                    |> List.unzip

                let g =
                    RoutingGraphData().Update descs (makeUpdatesMap updates) 0u

                let route = g.GetRoute a e Constants.DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual
                    (route |> hops2Ids)
                    ([ 1UL; 2UL; 3UL; 4UL ])
                    ""

            testCase "Calculate simple route" <| fun _ -> calculateRouteSimple()

            testCase "Calculate the shortest path (correct fees)"
            <| fun _ ->
                let amount = LNMoney.MilliSatoshis(10000L)
                let expectedCost = 10007L |> LNMoney.MilliSatoshis

                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            200u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.One,
                            200u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            300u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            400u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.One,
                            400u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.One,
                            100u,
                            Some(LNMoney.Zero),
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute a d amount

                let totalCost = totalRouteCost amount route

                Expect.sequenceEqual (hops2Ids(route)) [ 4UL; 5UL; 6UL ] ""
                Expect.equal totalCost expectedCost ""

            // FIXME: handle situations like this in future
            (*
                // Now channel 5 could route the amount (10000) but not the amount + fees (10007)
                let (desc, update) =
                    makeUpdate(
                        5UL,
                        e,
                        f,
                        LNMoney.One,
                        400u,
                        Some(LNMoney.Zero),
                        Some(LNMoney.MilliSatoshis(10005L)),
                        None
                    )

                let graph1 =
                    graph.Update
                        [desc]
                        (Map.ofList [ update.ShortChannelId, (ChannelUpdates.Empty.With { update with Timestamp = update.Timestamp + 1u }) ])
                        0u

                let route1 = graph1.GetRoute a d amount

                Expect.sequenceEqual (hops2Ids(route1)) [ 1UL; 2UL; 3UL ] ""
                *)

            testCase
                "calculate route considering the direct channel pays no fees"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(5L),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            a,
                            d,
                            LNMoney.MilliSatoshis(15L),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(5L),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(5L),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(5L),
                            0u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute a e DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual (hops2Ids(route)) [ 2UL; 5UL ] ""

            testCase "Blcklist channel"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                        makeUpdateSimple(4UL, d, e)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route1 = graph.GetRoute a e DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual
                    (hops2Ids(route1))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

                let graphWithRemovedEdge =
                    graph.BlacklistChannel <| ShortChannelId.FromUInt64(3UL)

                let route2 =
                    graphWithRemovedEdge.GetRoute a e DEFAULT_AMOUNT_MSAT

                Expect.isEmpty route2 ""

            let (h, i) =
                ("03de6411928b3b0217b50b27b269aea8457f7b88797402fff3e86f2d28775af5d5"
                 |> (hex.DecodeData >> PubKey >> NodeId),  // H
                 "03ffda25c95266e33c06c8006bbcd3985932a79580dfb07d95855c332a0e13b9ef"
                 |> (hex.DecodeData >> PubKey >> NodeId)) // I target

            testCase
                "find a route using channels with hltcMaximumMsat close to the payment amount"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(1UL, f, g, LNMoney.One, 0u, None, None, None)
                        makeUpdate(
                            2UL,
                            g,
                            h,
                            LNMoney.One,
                            0u,
                            None,
                            Some(
                                DEFAULT_AMOUNT_MSAT + LNMoney.MilliSatoshis(50L)
                            ),
                            None
                        )
                        makeUpdate(3UL, h, i, LNMoney.One, 0u, None, None, None)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute f i DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual (hops2Ids(route)) [ 1UL; 2UL; 3UL ] ""

            testCase
                "find a route using channels with htlcMinimumMsat close to the payment amount"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(1UL, f, g, LNMoney.One, 0u, None, None, None)
                        makeUpdate(
                            2UL,
                            g,
                            h,
                            LNMoney.One,
                            0u,
                            Some(
                                DEFAULT_AMOUNT_MSAT + LNMoney.MilliSatoshis(50L)
                            ),
                            None,
                            None
                        )
                        makeUpdate(3UL, h, i, LNMoney.One, 0u, None, None, None)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute f i DEFAULT_AMOUNT_MSAT

                Expect.isEmpty route ""

            testCase
                "if there are multiple channels between the same node, select the cheapest"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            f,
                            g,
                            LNMoney.Zero,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            g,
                            h,
                            LNMoney.MilliSatoshis(5L),
                            5u,
                            None,
                            None,
                            None
                        ) // expensive g -> h channel
                        makeUpdate(
                            6UL,
                            g,
                            h,
                            LNMoney.MilliSatoshis(0L),
                            0u,
                            None,
                            None,
                            None
                        ) // cheap     g -> h channel
                        makeUpdate(
                            3UL,
                            h,
                            i,
                            LNMoney.MilliSatoshis(0L),
                            0u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute f i DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual (hops2Ids(route)) [ 1UL; 6UL; 3UL ] ""

            testCase "Calculate longer but cheaper route"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                        makeUpdateSimple(4UL, d, e)
                        makeUpdate(
                            5UL,
                            b,
                            e,
                            LNMoney.MilliSatoshis(10L),
                            10u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute a e DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual (hops2Ids(route)) [ 1UL; 2UL; 3UL; 4UL ] ""

            testCase "route from node not present in graph"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(4UL, d, e)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                Expect.throwsT<System.ArgumentException>
                    (fun () -> graph.GetRoute a e DEFAULT_AMOUNT_MSAT |> ignore)
                    ""

            testCase "route not found (source OR target node not in graph)"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(4UL, c, d)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                Expect.throwsT<System.ArgumentException>
                    (fun () -> graph.GetRoute a d DEFAULT_AMOUNT_MSAT |> ignore)
                    ""

                let route2 = graph.GetRoute b e DEFAULT_AMOUNT_MSAT

                Expect.isEmpty route2 ""

            testCase "route not found (amount too high OR too low)"
            <| fun _ ->
                let highAmount = DEFAULT_AMOUNT_MSAT * 10
                let lowAmount = DEFAULT_AMOUNT_MSAT / 10

                let descsHi, updatesHi =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.Zero,
                            0u,
                            None,
                            Some(DEFAULT_AMOUNT_MSAT),
                            None
                        )
                        makeUpdateSimple(3UL, c, d)
                    ]
                    |> List.unzip

                let descsLow, updatesLow =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.Zero,
                            0u,
                            Some(DEFAULT_AMOUNT_MSAT),
                            None,
                            None
                        )
                        makeUpdateSimple(3UL, c, d)
                    ]
                    |> List.unzip

                let gHigh =
                    RoutingGraphData().Update
                        descsHi
                        (makeUpdatesMap updatesHi)
                        0u

                let gLow =
                    RoutingGraphData().Update
                        descsLow
                        (makeUpdatesMap updatesLow)
                        0u

                let route1 = gHigh.GetRoute a d highAmount

                Expect.isEmpty route1 ""

                let route2 = gLow.GetRoute a d lowAmount

                Expect.isEmpty route2 ""

            testCase "route to self"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute a a DEFAULT_AMOUNT_MSAT

                Expect.isEmpty route ""

            testCase "route to immediate neighbor"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                        makeUpdateSimple(4UL, d, e)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route = graph.GetRoute a b DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual (hops2Ids(route)) [ 1UL ] ""

            testCase "directed graph"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                        makeUpdateSimple(4UL, d, e)
                    ]
                    |> List.unzip
                // a -> e works, e -> a fails
                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route1 = graph.GetRoute a e DEFAULT_AMOUNT_MSAT

                Expect.sequenceEqual
                    (hops2Ids(route1))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

                let route2 = graph.GetRoute e a DEFAULT_AMOUNT_MSAT

                Expect.isEmpty route2 ""

            testCase "calculate route and return metadata"
            <| fun _ ->
                let uab =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(1UL)
                        Timestamp = 0u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(42L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2500L)
                        FeeProportionalMillionths = 140u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let uba =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(1UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(43L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2501L)
                        FeeProportionalMillionths = 141u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ubc =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(2UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(44L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2502L)
                        FeeProportionalMillionths = 142u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ucb =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(2UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(45L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2503L)
                        FeeProportionalMillionths = 143u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ucd =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(3UL)
                        Timestamp = 1u
                        MessageFlags = 1uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(46L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2504L)
                        FeeProportionalMillionths = 144u
                        HTLCMaximumMSat =
                            Some(LNMoney.MilliSatoshis(500000000L))
                    }

                let udc =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(3UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(47L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2505L)
                        FeeProportionalMillionths = 145u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ude =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(4UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(48L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2506L)
                        FeeProportionalMillionths = 146u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ued =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64(4UL)
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16(1us)
                        HTLCMinimumMSat = LNMoney.MilliSatoshis(49L)
                        FeeBaseMSat = LNMoney.MilliSatoshis(2507L)
                        FeeProportionalMillionths = 147u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let updates =
                    Map.empty
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(1UL)
                             A = a
                             B = b
                         })
                        uab
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(1UL)
                             A = b
                             B = a
                         })
                        uba
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(2UL)
                             A = b
                             B = c
                         })
                        ubc
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(2UL)
                             A = c
                             B = b
                         })
                        ucb
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(3UL)
                             A = c
                             B = d
                         })
                        ucd
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(3UL)
                             A = d
                             B = c
                         })
                        udc
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(4UL)
                             A = d
                             B = e
                         })
                        ude
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64(4UL)
                             A = e
                             B = d
                         })
                        ued

                let graph = 
                    RoutingGraphData().Update 
                        (updates |> Seq.map (fun pair -> pair.Key))
                        (updates |> Seq.map (fun pair -> pair.Value) |> makeUpdatesMap)
                        0u

                let hops = graph.GetRoute a e DEFAULT_AMOUNT_MSAT
                
                let expectedHops =
                    [
                        { Source = a; Target = b; Update = uab; ShortChannelId = uab.ShortChannelId }
                        { Source = b; Target = c; Update = ubc; ShortChannelId = ubc.ShortChannelId }
                        { Source = c; Target = d; Update = ucd; ShortChannelId = ucd.ShortChannelId }
                        { Source = d; Target = e; Update = ude; ShortChannelId = ude.ShortChannelId }
                    ]

                Expect.sequenceEqual hops expectedHops ""
        ] (*
            testCase "convert extra hops to assisted channels"
            <| fun _ ->
                let extraHop1 =
                    {
                        ExtraHop.NodeId = a
                        ShortChannelId = ShortChannelId.FromUInt64(1UL)
                        FeeBase = LNMoney.Satoshis(12L)
                        FeeProportionalMillionths = 10000u
                        CLTVExpiryDelta = BlockHeightOffset16(12us)
                    }

                let extraHop2 =
                    {
                        ExtraHop.NodeId = b
                        ShortChannelId = ShortChannelId.FromUInt64(2UL)
                        FeeBase = LNMoney.Satoshis(200L)
                        FeeProportionalMillionths = 0u
                        CLTVExpiryDelta = BlockHeightOffset16(22us)
                    }

                let extraHop3 =
                    {
                        ExtraHop.NodeId = c
                        ShortChannelId = ShortChannelId.FromUInt64(3UL)
                        FeeBase = LNMoney.Satoshis(150L)
                        FeeProportionalMillionths = 0u
                        CLTVExpiryDelta = BlockHeightOffset16(32us)
                    }

                let extraHop4 =
                    {
                        ExtraHop.NodeId = d
                        ShortChannelId = ShortChannelId.FromUInt64(4UL)
                        FeeBase = LNMoney.Satoshis(50L)
                        FeeProportionalMillionths = 0u
                        CLTVExpiryDelta = BlockHeightOffset16(42us)
                    }

                let extraHops =
                    [
                        extraHop1
                        extraHop2
                        extraHop3
                        extraHop4
                    ]

                let amount = LNMoney.Satoshis(900L) // below RoutingHeuristics.CAPACITY_CHANNEL_LOW

                let acs =
                    Routing.toAssistedChannels e amount extraHops |> Map.ofSeq

                Expect.equal
                    (acs.[extraHop4.ShortChannelId])
                    ({
                         AssistedChannel.ExtraHop = extraHop4
                         NextNodeId = e
                         HTLCMaximum = (LNMoney.Satoshis(1050L))
                     })
                    ""

                Expect.equal
                    (acs.[extraHop3.ShortChannelId])
                    ({
                         AssistedChannel.ExtraHop = extraHop3
                         NextNodeId = d
                         HTLCMaximum = (LNMoney.Satoshis(1200L))
                     })
                    ""

                Expect.equal
                    (acs.[extraHop2.ShortChannelId])
                    ({
                         AssistedChannel.ExtraHop = extraHop2
                         NextNodeId = c
                         HTLCMaximum = (LNMoney.Satoshis(1400L))
                     })
                    ""

                Expect.equal
                    (acs.[extraHop1.ShortChannelId])
                    ({
                         AssistedChannel.ExtraHop = extraHop1
                         NextNodeId = b
                         HTLCMaximum = (LNMoney.Satoshis(1426L))
                     })
                    ""

            testCase "blacklist routes"
            <| fun _ ->
                let updates =
                    [
                        makeUpdateSimple(1UL, a, b)
                        makeUpdateSimple(2UL, b, c)
                        makeUpdateSimple(3UL, c, d)
                        makeUpdateSimple(4UL, d, e)
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let ignoredE =
                    Set.singleton(
                        {
                            ShortChannelId = ShortChannelId.FromUInt64(3UL)
                            A = c
                            B = d
                        }
                    )

                let route1 =
                    Routing.findRoute
                        (g)
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (ignoredE)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))

                Expect.isError (Result.ToFSharpCoreResult route1) ""

                // verify that we left the graph untouched
                Expect.isTrue
                    (g.ContainsEdge(makeUpdateSimple(3UL, c, d) |> fst))
                    ""

                Expect.isTrue (g.ContainsVertex(c)) ""
                Expect.isTrue (g.ContainsVertex(d)) ""

                // make sure we can find a route without the blacklist
                let route2 =
                    Routing.findRoute
                        g
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route2))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

            testCase
                "route to a destination that is not in the graph (with assisted routes)"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(10L),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(10L),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(10L),
                            10u,
                            None,
                            None,
                            None
                        )
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route =
                    Routing.findRoute
                        (g)
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))

                Expect.isError
                    (Result.ToFSharpCoreResult route)
                    "there should be no e node in the graph"

                // now we add the missing edge to reach the destination
                let (extraDesc, extraUpdate) =
                    makeUpdate(
                        4UL,
                        d,
                        e,
                        LNMoney.MilliSatoshis(5L),
                        5u,
                        None,
                        None,
                        None
                    )

                let extraGraphEdges =
                    Set.singleton(
                        {
                            GraphLabel.Desc = extraDesc
                            Update = extraUpdate
                        }
                    )

                let route1 =
                    Routing.findRoute
                        g
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (extraGraphEdges)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route1))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

            testCase
                "Verify that extra hops takes precedence over known channels"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route1 =
                    Routing.findRoute
                        g
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route1))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

                Expect.equal
                    ((route1 |> Seq.item 1).LastUpdateValue.FeeBaseMSat)
                    (LNMoney.MilliSatoshis(10))
                    ""

                let (extraDesc, extraUpdate) =
                    makeUpdate(
                        2UL,
                        b,
                        c,
                        LNMoney.MilliSatoshis(5),
                        5u,
                        None,
                        None,
                        None
                    )

                let extraGraphEdges =
                    Set.singleton(
                        {
                            GraphLabel.Desc = extraDesc
                            Update = extraUpdate
                        }
                    )

                let route2 =
                    Routing.findRoute
                        g
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        extraGraphEdges
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route2))
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

                Expect.equal
                    ((route2 |> Seq.item 1).LastUpdateValue.FeeBaseMSat)
                    (LNMoney.MilliSatoshis(5))
                    ""

            testPropertyWithConfig fsCheckConfig "compute ignored channels"
            <| fun (f: NodeId, g: NodeId, h: NodeId, i: NodeId, j: NodeId) ->
                let channels =
                    Map.empty
                    |> Map.add
                        (ShortChannelId.FromUInt64(1UL))
                        (makeChannelAnn(1UL, a, b))
                    |> Map.add
                        (ShortChannelId.FromUInt64(2UL))
                        (makeChannelAnn(2UL, b, c))
                    |> Map.add
                        (ShortChannelId.FromUInt64(3UL))
                        (makeChannelAnn(3UL, c, d))
                    |> Map.add
                        (ShortChannelId.FromUInt64(4UL))
                        (makeChannelAnn(4UL, d, e))
                    |> Map.add
                        (ShortChannelId.FromUInt64(5UL))
                        (makeChannelAnn(5UL, f, g))
                    |> Map.add
                        (ShortChannelId.FromUInt64(6UL))
                        (makeChannelAnn(6UL, f, h))
                    |> Map.add
                        (ShortChannelId.FromUInt64(7UL))
                        (makeChannelAnn(7UL, h, i))
                    |> Map.add
                        (ShortChannelId.FromUInt64(8UL))
                        (makeChannelAnn(8UL, i, j))

                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            c,
                            b,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            f,
                            g,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            h,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            7UL,
                            h,
                            i,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            8UL,
                            i,
                            j,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                    ]

                let publicChannels =
                    channels
                    |> Map.map(fun scid ann ->
                        let (_, update) =
                            updates
                            |> Seq.find(fun (upd, _) ->
                                upd.ShortChannelId = scid
                            )

                        let (maybeUpdate1, maybeUpdate2) =
                            if (update.ChannelFlags &&& 1uy = 1uy) then
                                (Some(update), None)
                            else
                                (None, Some(update))

                        let pc =
                            PublicChannel.Create(
                                ann,
                                TxId.Zero,
                                Money.Satoshis(1000L),
                                maybeUpdate1,
                                maybeUpdate2
                            )

                        (pc)
                    )

                let ignored =
                    Routing.getIgnoredChannelDesc
                        (publicChannels)
                        (Set [ c; j; (NodeId((new Key()).PubKey)) ])
                    |> Set

                Expect.isTrue
                    (ignored.Contains(
                        {
                            ChannelDesc.ShortChannelId =
                                ShortChannelId.FromUInt64(2UL)
                            A = b
                            B = c
                        }
                    ))
                    ""

                Expect.isTrue
                    (ignored.Contains(
                        {
                            ChannelDesc.ShortChannelId =
                                ShortChannelId.FromUInt64(2UL)
                            A = c
                            B = b
                        }
                    ))
                    ""

                Expect.isTrue
                    (ignored.Contains(
                        {
                            ChannelDesc.ShortChannelId =
                                ShortChannelId.FromUInt64(3UL)
                            A = c
                            B = d
                        }
                    ))
                    ""

                Expect.isTrue
                    (ignored.Contains(
                        {
                            ChannelDesc.ShortChannelId =
                                ShortChannelId.FromUInt64(8UL)
                            A = i
                            B = j
                        }
                    ))
                    ""

            testCase "limit routes to 20 hops"
            <| fun () ->
                let nodes =
                    [
                        for _ in 0..22 -> (new Key()).PubKey |> NodeId
                    ]

                let updates =
                    Seq.zip
                        (nodes |> List.rev |> List.skip 1 |> List.rev)
                        (nodes |> Seq.skip 1) // (0, 1) :: (1, 2) :: ...
                    |> Seq.mapi(fun i (na, nb) ->
                        makeUpdate(
                            (uint64 i),
                            na,
                            nb,
                            LNMoney.MilliSatoshis(5),
                            0u,
                            None,
                            None,
                            None
                        )
                    )

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let r18 =
                    (Routing.findRoute
                        g
                        (nodes.[0])
                        nodes.[18]
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u)))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(r18))
                    [ for i in 0..17 -> (uint64 i) ]
                    ""

                let r19 =
                    (Routing.findRoute
                        g
                        (nodes.[0])
                        nodes.[19]
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u)))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(r19))
                    [ for i in 0..18 -> (uint64 i) ]
                    ""

                let r20 =
                    (Routing.findRoute
                        g
                        (nodes.[0])
                        nodes.[20]
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u)))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(r20))
                    [ for i in 0..19 -> (uint64 i) ]
                    ""

                let r21 =
                    (Routing.findRoute
                        g
                        (nodes.[0])
                        nodes.[21]
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u)))

                Expect.isError (Result.ToFSharpCoreResult r21) ""

            testCase "ignore cheaper route when it has more than 20 hops"
            <| fun _ ->
                let nodes =
                    [
                        for _ in 0..50 -> (new Key()).PubKey |> NodeId
                    ]

                let updates =
                    List.zip
                        (nodes |> List.rev |> List.skip 1 |> List.rev)
                        (nodes |> List.skip 1) // (0, 1) :: (1, 2) :: ...
                    |> List.mapi(fun i (na, nb) ->
                        makeUpdate(
                            (uint64 i),
                            na,
                            nb,
                            LNMoney.One,
                            0u,
                            None,
                            None,
                            None
                        )
                    )

                // add expensive but shorter route
                let updates2 =
                    (makeUpdate(
                        99UL,
                        nodes.[2],
                        nodes.[48],
                        LNMoney.MilliSatoshis(1000L),
                        0u,
                        None,
                        None,
                        None
                    ))
                    :: updates

                let g = DirectedLNGraph.Create().AddEdges(updates2)

                let route =
                    Routing.findRoute
                        g
                        nodes.[0]
                        nodes.[49]
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route))
                    [ 0UL; 1UL; 99UL; 48UL ]
                    ""

            testCase
                "ignore cheaper route when it has more than the requested CLTV limit"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(50us))
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(50us))
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(50us))
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(9us))
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis(5),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(9us))
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis(5),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(9us))
                        )
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route =
                    Routing.findRoute
                        (g)
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        { DEFAULT_ROUTE_PARAMS with
                            RouteMaxCLTV = (BlockHeightOffset16(28us))
                        }
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual (hops2Ids(route)) [ 4UL; 5UL; 6UL ] ""

            testCase
                "ignore cheaper route when it grows longer than the requested size"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.MilliSatoshis(5)),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                        makeUpdate(
                            6UL,
                            b,
                            f,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.MilliSatoshis(5)),
                            None,
                            (Some(BlockHeightOffset16(9us)))
                        )
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route =
                    Routing.findRoute
                        g
                        a
                        f
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        { DEFAULT_ROUTE_PARAMS with
                            RouteMaxLength = 3
                        }
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual (hops2Ids(route)) [ 1UL; 6UL ] ""

            testCase "ignore loops"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            a,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route1 =
                    Routing.findRoute
                        g
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (hops2Ids(route1))
                    [ 1UL; 2UL; 4UL; 5UL ]
                    ""

            testCase
                "ensure the route calculation terminates correctly when selecting 0-fees edges"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(10),
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdateSimple(3UL, b, e)
                        makeUpdateSimple(6UL, e, f)
                        makeUpdateSimple(6UL, f, e)
                        makeUpdateSimple(5UL, e, d)
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let route1 =
                    Routing.findRoute
                        g
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual (hops2Ids(route1)) [ 1UL; 3UL; 5UL ] ""

            // +---+            +---+            +---+
            // | A +-----+      | B +----------> | C |
            // +-+-+     |      +-+-+            +-+-+
            //   ^       |        ^                |
            //   |       |        |                |
            //   |       v----> + |                |
            // +-+-+            <-+-+            +-+-+
            // | D +----------> | E +----------> | F |
            // +---+            +---+            +---+
            //
            testCase "find the k-shortest paths in a graph, k = 4"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(1UL, d, a, LNMoney.One, 0u, None, None, None)
                        makeUpdate(2UL, d, e, LNMoney.One, 0u, None, None, None)
                        makeUpdate(3UL, a, e, LNMoney.One, 0u, None, None, None)
                        makeUpdate(4UL, e, b, LNMoney.One, 0u, None, None, None)
                        makeUpdate(5UL, e, f, LNMoney.One, 0u, None, None, None)
                        makeUpdate(6UL, b, c, LNMoney.One, 0u, None, None, None)
                        makeUpdate(7UL, c, f, LNMoney.One, 0u, None, None, None)
                    ]

                let g = DirectedLNGraph.Create().AddEdges(updates)

                let fourShortestPaths =
                    Graph.yenKShortestPaths
                        g
                        d
                        f
                        DEFAULT_AMOUNT_MSAT
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        4
                        None
                        (BlockHeight.One)
                        (fun _ -> true)
                    |> Seq.toList

                Expect.equal
                    (fourShortestPaths.Length)
                    4
                    (sprintf "found shortest paths were %A" fourShortestPaths)

                let actuals =
                    [
                        for i in 0..3 do
                            fourShortestPaths.[i].Path
                            |> Seq.map ChannelHop.FromGraphEdge
                            |> hops2Ids
                    ]

                Expect.sequenceEqual actuals.[0] [ 2UL; 5UL ] ""
                Expect.sequenceEqual actuals.[1] [ 1UL; 3UL; 5UL ] ""
                Expect.sequenceEqual actuals.[2] [ 2UL; 4UL; 6UL; 7UL ] ""
                Expect.sequenceEqual actuals.[3] [ 1UL; 3UL; 4UL; 6UL; 7UL ] ""

            testCase "find the k shortest path (wikipedia example)"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            10UL,
                            c,
                            e,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            20UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(3),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            30UL,
                            d,
                            f,
                            LNMoney.MilliSatoshis(4),
                            5u,
                            None,
                            None,
                            None
                        ) // D -> F has a higher cost to distinguish from the 2nd cheapest route
                        makeUpdate(
                            40UL,
                            e,
                            d,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            50UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            60UL,
                            e,
                            g,
                            LNMoney.MilliSatoshis(3),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            70UL,
                            f,
                            g,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            None,
                            None,
                            None
                        )

                        makeUpdate(
                            80UL,
                            f,
                            h,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            90UL,
                            g,
                            h,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            None,
                            None,
                            None
                        )
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let twoShortestPaths =
                    Graph.yenKShortestPaths
                        graph
                        c
                        h
                        DEFAULT_AMOUNT_MSAT
                        Set.empty
                        Set.empty
                        Set.empty
                        2
                        None
                        (BlockHeight(0u))
                        (fun _ -> true)
                    |> Seq.toList

                Expect.equal (twoShortestPaths.Length) 2 ""
                let shortest = twoShortestPaths.[0]

                Expect.sequenceEqual
                    (shortest.Path
                     |> Seq.map(ChannelHop.FromGraphEdge)
                     |> hops2Ids)
                    [ 10UL; 50UL; 80UL ]
                    ""

                let secondShortest = twoShortestPaths.[1]

                Expect.sequenceEqual
                    (secondShortest.Path
                     |> Seq.map(ChannelHop.FromGraphEdge)
                     |> hops2Ids)
                    [ 10UL; 60UL; 90UL ]
                    ""

            testCase
                "terminate looking for k-shortest path if there are no more alternative paths than k, must not consider routes going back on their steps"
            <| fun _ ->
                // simple graph with only 2 possible paths from A to F
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            1UL,
                            b,
                            a,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            c,
                            b,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            f,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            f,
                            c,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            d,
                            c,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            41UL,
                            d,
                            c,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        ) // there is more than one D -> C channel
                        makeUpdate(
                            5UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            e,
                            d,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            e,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let foundPaths =
                    Graph.yenKShortestPaths
                        graph
                        a
                        f
                        DEFAULT_AMOUNT_MSAT
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        3
                        None
                        (BlockHeight 0u)
                        (fun _ -> true)
                    |> Seq.toList

                Expect.equal (foundPaths.Length) 2 ""

                Expect.sequenceEqual
                    (foundPaths.[0].Path
                     |> Seq.map(ChannelHop.FromGraphEdge)
                     |> hops2Ids)
                    [ 1UL; 2UL; 3UL ]
                    ""

                Expect.sequenceEqual
                    (foundPaths.[1].Path
                     |> Seq.map(ChannelHop.FromGraphEdge)
                     |> hops2Ids)
                    [ 1UL; 2UL; 4UL; 5UL; 6UL ]
                    ""

            testCase "select a random route below the requested fee"
            <| fun _ ->
                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(3),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis(3),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis(3),
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            7UL,
                            e,
                            c,
                            LNMoney.MilliSatoshis(9),
                            0u,
                            None,
                            None,
                            None
                        )
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let strictFeeParams =
                    { DEFAULT_ROUTE_PARAMS with
                        MaxFeeBase = LNMoney.MilliSatoshis(7)
                        MaxFeePCT = 0.
                    }

                for _ in 0..10 do
                    let r =
                        Routing.findRoute
                            graph
                            a
                            d
                            DEFAULT_AMOUNT_MSAT
                            3
                            (Set.empty)
                            (Set.empty)
                            (Set.empty)
                            strictFeeParams
                            (BlockHeight(400000u))

                    Expect.isOk (Result.ToFSharpCoreResult r) ""
                    let someRoute = r |> Result.deref

                    let routeCost =
                        (Graph.pathWeight
                            (hops2Edges(someRoute))
                            DEFAULT_AMOUNT_MSAT
                            false
                            (BlockHeight 0u)
                            None)
                            .Cost
                        - DEFAULT_AMOUNT_MSAT

                    let costMSat = routeCost.MilliSatoshi
                    Expect.isTrue (costMSat = 5L || costMSat = 6L) ""

            testCase "Use weight ratios to when computing the edge weight"
            <| fun _ ->
                let largeCap = LNMoney.MilliSatoshis(8000000000L)

                let updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis(0),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(13us))
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.MilliSatoshis(0),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(12us))
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(500us))
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis(1),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(500us))
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(9us))
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            Some(LNMoney.Zero),
                            None,
                            Some(BlockHeightOffset16(9us))
                        )
                        makeUpdate(
                            7UL,
                            e,
                            c,
                            LNMoney.MilliSatoshis(2),
                            0u,
                            Some(LNMoney.Zero),
                            Some(largeCap),
                            Some(BlockHeightOffset16(12us))
                        )
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let r =
                    Routing.findRoute
                        graph
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        0
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        DEFAULT_ROUTE_PARAMS
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (r |> hops2Nodes)
                    [ (a, b); (b, c); (c, d) ]
                    ""

                let routeClTVOptimized =
                    let p =
                        let r =
                            WeightRatios.TryCreate(1., 0., 0.) |> Result.deref

                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = Some(r)
                        }

                    Routing.findRoute
                        graph
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        0
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        p
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (routeClTVOptimized |> hops2Nodes)
                    [ (a, e); (e, f); (f, d) ]
                    ""

                let routeCapOptimized =
                    let p =
                        let r =
                            WeightRatios.TryCreate(0., 0., 1.) |> Result.deref

                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = Some(r)
                        }

                    Routing.findRoute
                        graph
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        0
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        p
                        (BlockHeight(400000u))
                    |> Result.deref

                Expect.sequenceEqual
                    (routeCapOptimized |> hops2Nodes)
                    [ (a, e); (e, c); (c, d) ]
                    ""

            testCase
                "Prefer going through an older channel if fees and CLTV are the same"
            <| fun _ ->
                let currentBlockHeight = 554000u

                let mu(schid, one, two) =
                    makeUpdate2(
                        schid,
                        one,
                        two,
                        LNMoney.MilliSatoshis(1),
                        0u,
                        (Some LNMoney.Zero),
                        None,
                        (Some(BlockHeightOffset16(144us)))
                    )

                let updates =
                    [
                        mu((sprintf "%ix0x1" currentBlockHeight), a, b)
                        mu((sprintf "%ix0x4" currentBlockHeight), a, e)
                        mu(
                            (sprintf "%ix0x2" (currentBlockHeight - 3000u)),
                            b,
                            c
                        ) // younger channel
                        mu(
                            (sprintf "%ix0x3" (currentBlockHeight - 3000u)),
                            c,
                            d
                        )
                        mu((sprintf "%ix0x5" currentBlockHeight), e, f)
                        mu((sprintf "%ix0x6" currentBlockHeight), f, d)
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = Some(wr)
                        }

                    Routing.findRoute
                        graph
                        a
                        d
                        (DEFAULT_AMOUNT_MSAT / 2)
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        rp
                        (BlockHeight(currentBlockHeight))
                    |> Result.deref
                    |> hops2Nodes

                Expect.sequenceEqual
                    routeScoreOptimized
                    [ (a, b); (b, c); (c, d) ]
                    ""

            testCase
                "prefer a route with a smaller total CLTV if fees and scores are the same"
            <| fun _ ->
                let mu(schid, one, two, cltv) =
                    makeUpdate(
                        schid,
                        one,
                        two,
                        LNMoney.One,
                        0u,
                        (Some LNMoney.Zero),
                        None,
                        (Some(BlockHeightOffset16 cltv))
                    )

                let updates =
                    [
                        mu(1UL, a, b, 12us)
                        mu(4UL, a, e, 12us)
                        mu(2UL, b, c, 10us) // smaller cltv
                        mu(3UL, c, d, 12us)
                        mu(5UL, e, f, 12us)
                        mu(6UL, f, d, 12us)
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = Some(wr)
                        }

                    Routing.findRoute
                        graph
                        a
                        d
                        (DEFAULT_AMOUNT_MSAT / 2)
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        rp
                        (BlockHeight(400000u))
                    |> Result.deref
                    |> hops2Nodes

                Expect.sequenceEqual
                    routeScoreOptimized
                    [ (a, b); (b, c); (c, d) ]
                    ""

                ()

            testCase "avoid a route that breaks off the max CLTV"
            <| fun _ ->
                let mu(schid, one, two, cltv) =
                    makeUpdate(
                        schid,
                        one,
                        two,
                        LNMoney.One,
                        0u,
                        (Some LNMoney.Zero),
                        None,
                        (Some(BlockHeightOffset16 cltv))
                    )
                // A --> B --> C --> D is cheaper but has a total CLTV > 2016!
                // A --> E --> F --> D is more expensive but has a total CLTV < 2016
                let updates =
                    [
                        mu(1UL, a, b, 144us)
                        mu(4UL, a, e, 144us)
                        mu(2UL, b, c, 1000us)
                        mu(3UL, c, d, 900us)
                        mu(5UL, e, f, 144us)
                        mu(6UL, f, d, 144us)
                    ]

                let graph = DirectedLNGraph.Create().AddEdges(updates)

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = Some(wr)
                        }

                    Routing.findRoute
                        graph
                        a
                        d
                        (DEFAULT_AMOUNT_MSAT / 2)
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        rp
                        (BlockHeight(400000u))
                    |> Result.deref
                    |> hops2Nodes

                Expect.sequenceEqual
                    routeScoreOptimized
                    [ (a, e); (e, f); (f, d) ]
                    ""

            testCase "cost function is monotonic"
            <| fun _ ->
                // This test have a channel (542280x2156x0) that according to heuristics is very convenient but actually useless to reach the target,
                // then if the cost function is not monotonic the path-finding breaks because the result path contains a loop.
                let updates =
                    let m = Map.empty

                    let m =
                        let shortChannelId1 =
                            ShortChannelId.ParseUnsafe("565643x1216x0")

                        let pk1 =
                            PubKey(
                                "03864ef025fde8fb587d989186ce6a4a186895ee44a926bfc370e2c366597a3f8f"
                            )
                            |> NodeId

                        let pk2 =
                            PubKey(
                                "024655b768ef40951b20053a5c4b951606d4d86085d51238f2c67c7dec29c792ca"
                            )
                            |> NodeId

                        let channelAnn =
                            makeChannelAnnCore(shortChannelId1, pk1, pk2)

                        let unsignedChannelUpdate1 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId1
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 0uy
                                CLTVExpiryDelta = BlockHeightOffset16(14us)
                                HTLCMinimumMSat = LNMoney.One
                                FeeBaseMSat = LNMoney.Satoshis(1L)
                                FeeProportionalMillionths = 10u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(4294967295L))
                            }

                        let unsignedChannelUpdate2 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId1
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 1uy
                                CLTVExpiryDelta = BlockHeightOffset16(144us)
                                HTLCMinimumMSat = LNMoney.Zero
                                FeeBaseMSat = LNMoney.Satoshis(1L)
                                FeeProportionalMillionths = 100u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(15000000000L))
                            }

                        let pc1 =
                            PublicChannel.Create(
                                channelAnn,
                                TxId.Zero,
                                Money.Zero,
                                Some(unsignedChannelUpdate1),
                                Some(unsignedChannelUpdate2)
                            )

                        m |> Map.add (shortChannelId1) pc1

                    let m =
                        let shortChannelId2 =
                            ShortChannelId.ParseUnsafe("542280x2156x0")

                        let pk1 =
                            PubKey(
                                "03864ef025fde8fb587d989186ce6a4a186895ee44a926bfc370e2c366597a3f8f"
                            )
                            |> NodeId

                        let pk2 =
                            PubKey(
                                "03cb7983dc247f9f81a0fa2dfa3ce1c255365f7279c8dd143e086ca333df10e278"
                            )
                            |> NodeId

                        let channelAnn =
                            makeChannelAnnCore(shortChannelId2, pk1, pk2)

                        let unsignedChannelUpdate1 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId2
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 0uy
                                CLTVExpiryDelta = BlockHeightOffset16(144us)
                                HTLCMinimumMSat = LNMoney.Satoshis(1)
                                FeeBaseMSat = LNMoney.Satoshis(1L)
                                FeeProportionalMillionths = 100u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(16777000000L))
                            }

                        let unsignedChannelUpdate2 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId2
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 1uy
                                CLTVExpiryDelta = BlockHeightOffset16(144us)
                                HTLCMinimumMSat = LNMoney.One
                                FeeBaseMSat = LNMoney.Satoshis(667)
                                FeeProportionalMillionths = 1u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(16777000000L))
                            }

                        let pc2 =
                            PublicChannel.Create(
                                channelAnn,
                                TxId.Zero,
                                Money.Zero,
                                Some(unsignedChannelUpdate1),
                                Some(unsignedChannelUpdate2)
                            )

                        m |> Map.add (shortChannelId2) pc2

                    let m =
                        let shortChannelId3 =
                            ShortChannelId.ParseUnsafe("565779x2711x0")

                        let pk1 =
                            PubKey(
                                "036d65409c41ab7380a43448f257809e7496b52bf92057c09c4f300cbd61c50d96"
                            )
                            |> NodeId

                        let pk2 =
                            PubKey(
                                "03864ef025fde8fb587d989186ce6a4a186895ee44a926bfc370e2c366597a3f8f"
                            )
                            |> NodeId

                        let channelAnn =
                            makeChannelAnnCore(shortChannelId3, pk1, pk2)

                        let unsignedChannelUpdate1 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId3
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 0uy
                                CLTVExpiryDelta = BlockHeightOffset16(144us)
                                HTLCMinimumMSat = LNMoney.One
                                FeeBaseMSat = LNMoney.Satoshis(1L)
                                FeeProportionalMillionths = 100u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(230000000L))
                            }

                        let unsignedChannelUpdate2 =
                            {
                                UnsignedChannelUpdateMsg.ChainHash =
                                    uint256.Zero
                                ShortChannelId = shortChannelId3
                                Timestamp = 0u
                                MessageFlags = 1uy
                                ChannelFlags = 3uy
                                CLTVExpiryDelta = BlockHeightOffset16(144us)
                                HTLCMinimumMSat = LNMoney.One
                                FeeBaseMSat = LNMoney.Satoshis(1)
                                FeeProportionalMillionths = 100u
                                HTLCMaximumMSat =
                                    Some(LNMoney.MilliSatoshis(230000000L))
                            }

                        let pc3 =
                            PublicChannel.Create(
                                channelAnn,
                                TxId.Zero,
                                Money.Zero,
                                Some(unsignedChannelUpdate1),
                                Some(unsignedChannelUpdate2)
                            )

                        m |> Map.add (shortChannelId3) pc3

                    m

                let graph = DirectedLNGraph.MakeGraph(updates)

                let routeParams =
                    {
                        RouteParams.Randomize = false
                        MaxFeeBase = LNMoney.MilliSatoshis 21000
                        MaxFeePCT = 0.03
                        RouteMaxLength = 6
                        RouteMaxCLTV = 1008us |> BlockHeightOffset16
                        Ratios =
                            Some(
                                WeightRatios.TryCreate(0.15, 0.35, 0.5)
                                |> Result.deref
                            )
                    }

                let thisNode =
                    PubKey(
                        "036d65409c41ab7380a43448f257809e7496b52bf92057c09c4f300cbd61c50d96"
                    )
                    |> NodeId

                let targetNode =
                    PubKey(
                        "024655b768ef40951b20053a5c4b951606d4d86085d51238f2c67c7dec29c792ca"
                    )
                    |> NodeId

                let amount = 351000 |> LNMoney.MilliSatoshis

                let route =
                    Routing.findRoute
                        graph
                        thisNode
                        targetNode
                        amount
                        1
                        (Set.empty)
                        (Set.empty)
                        (Set.empty)
                        routeParams
                        (BlockHeight(567634u))
                    |> Result.deref
                    |> Seq.toList

                Expect.equal (route.Length) 2 ""
                Expect.equal (route |> List.last).NextNodeIdValue targetNode ""
        ]
*)
