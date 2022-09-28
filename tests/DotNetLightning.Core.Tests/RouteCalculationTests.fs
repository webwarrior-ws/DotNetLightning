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

    let DEFAULT_ROUTE_PARAMS = RouteParams.Default

let fsCheckConfig =
    { FsCheckConfig.defaultConfig with
        arbitrary = [ typeof<PrimitiveGenerators> ]
        maxTest = 2
    }

let makeChannelAnnCore(shortChannelId: ShortChannelId, nodeIdA, nodeIdB) =
    let isNode1(localNodeId: NodeId, remoteNodeId: NodeId) =
        localNodeId > remoteNodeId

    let nodeId1, nodeId2 =
        if isNode1(nodeIdA, nodeIdB) then
            nodeIdA, nodeIdB
        else
            nodeIdB, nodeIdA

    {
        UnsignedChannelAnnouncementMsg.ShortChannelId = shortChannelId
        NodeId1 = nodeId1
        NodeId2 = nodeId2
        BitcoinKey1 = (new Key()).PubKey |> ComparablePubKey
        BitcoinKey2 = (new Key()).PubKey |> ComparablePubKey
        ChainHash = Network.RegTest.GenesisHash
        Features = FeatureBits.Zero
        ExcessData = [||]
    }

let makeChannelAnn(shortChannelId: uint64, nodeIdA: NodeId, nodeIdB: NodeId) =
    makeChannelAnnCore(
        ShortChannelId.FromUInt64 shortChannelId,
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

let hops2Ids(route: seq<IRoutingHopInfo>) =
    route
    |> Seq.map(fun hop ->
        hop.ShortChannelId.ToBytes()
        |> fun x -> NBitcoin.Utils.ToUInt64(x, false)
    )

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
    let cltvDelta = Option.defaultValue (BlockHeightOffset16 0us) cltvDelta

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

let makeUpdate2(s, a, b, feeBase, feeProp, minHTLC, maxHTLC, cltvDelta) =
    makeUpdateCore(
        ShortChannelId.ParseUnsafe s,
        a,
        b,
        feeBase,
        feeProp,
        minHTLC,
        maxHTLC,
        cltvDelta
    )

let makeUpdateSimple(shortChannelId, a, b) =
    makeUpdate(shortChannelId, a, b, LNMoney.Zero, 0u, None, None, None)

let makeUpdatesMap(updateMsgs: seq<UnsignedChannelUpdateMsg>) =
    let mutable updatesMap: Map<ShortChannelId, ChannelUpdates> = Map.empty

    for updMsg in updateMsgs do
        let oldValue =
            match updatesMap |> Map.tryFind updMsg.ShortChannelId with
            | Some updates -> updates
            | None -> ChannelUpdates.Empty

        updatesMap <-
            updatesMap |> Map.add updMsg.ShortChannelId (oldValue.With updMsg)

    updatesMap

let totalRouteCost (amount: LNMoney) (route: seq<IRoutingHopInfo>) =
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
            let calculateRouteSimple routeParams =
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 1L,
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 1L,
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 1L,
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis 1L,
                            10u,
                            None,
                            None,
                            BlockHeightOffset16.One |> Some
                        )
                    ]
                    |> List.unzip

                let g =
                    RoutingGraphData().Update descs (makeUpdatesMap updates) 0u

                let route =
                    g.GetRoute
                        a
                        e
                        Constants.DEFAULT_AMOUNT_MSAT
                        400000u
                        routeParams
                        []

                Expect.sequenceEqual
                    (route |> hops2Ids)
                    [ 1UL; 2UL; 3UL; 4UL ]
                    ""

            testCase "Calculate simple route"
            <| fun _ -> calculateRouteSimple DEFAULT_ROUTE_PARAMS

            testCase "Check fee against max pct properly"
            <| fun _ ->
                // fee is acceptable if it is either
                // - below our maximum fee base
                // - below our maximum fraction of the paid amount

                // here we have a maximum fee base of 1 msat, and all our updates have a base fee of 10 msat
                // so our fee will always be above the base fee, and we will always check that it is below our maximum percentage
                // of the amount being paid
                calculateRouteSimple
                    { DEFAULT_ROUTE_PARAMS with
                        MaxFeeBase = LNMoney.One
                    }

            testCase "Calculate the shortest path (correct fees)"
            <| fun _ ->
                let amount = LNMoney.MilliSatoshis 10000L
                let expectedCost = 10007L |> LNMoney.MilliSatoshis

                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            200u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.One,
                            200u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            300u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            400u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.One,
                            400u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.One,
                            100u,
                            Some LNMoney.Zero,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute a d amount 400000u DEFAULT_ROUTE_PARAMS []

                let totalCost = totalRouteCost amount route

                Expect.sequenceEqual (hops2Ids route) [ 4UL; 5UL; 6UL ] ""
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
                            LNMoney.MilliSatoshis 5L,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            a,
                            d,
                            LNMoney.MilliSatoshis 15L,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 5L,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 5L,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis 5L,
                            0u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route) [ 2UL; 5UL ] ""

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

                let route1 =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route1) [ 1UL; 2UL; 3UL; 4UL ] ""

                let graphWithRemovedEdge =
                    graph.BlacklistChannel <| ShortChannelId.FromUInt64 3UL

                let route2 =
                    graphWithRemovedEdge.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

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
                                DEFAULT_AMOUNT_MSAT + LNMoney.MilliSatoshis 50L
                            ),
                            None
                        )
                        makeUpdate(3UL, h, i, LNMoney.One, 0u, None, None, None)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        f
                        i
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route) [ 1UL; 2UL; 3UL ] ""

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
                                DEFAULT_AMOUNT_MSAT + LNMoney.MilliSatoshis 50L
                            ),
                            None,
                            None
                        )
                        makeUpdate(3UL, h, i, LNMoney.One, 0u, None, None, None)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        f
                        i
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

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
                            LNMoney.MilliSatoshis 5L,
                            5u,
                            None,
                            None,
                            None
                        ) // expensive g -> h channel
                        makeUpdate(
                            6UL,
                            g,
                            h,
                            LNMoney.MilliSatoshis 0L,
                            0u,
                            None,
                            None,
                            None
                        ) // cheap     g -> h channel
                        makeUpdate(
                            3UL,
                            h,
                            i,
                            LNMoney.MilliSatoshis 0L,
                            0u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        f
                        i
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route) [ 1UL; 6UL; 3UL ] ""

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
                            LNMoney.MilliSatoshis 10L,
                            10u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route) [ 1UL; 2UL; 3UL; 4UL ] ""

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
                    (fun () ->
                        graph.GetRoute
                            a
                            e
                            DEFAULT_AMOUNT_MSAT
                            400000u
                            DEFAULT_ROUTE_PARAMS
                            []
                        |> ignore
                    )
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
                    (fun () ->
                        graph.GetRoute
                            a
                            d
                            DEFAULT_AMOUNT_MSAT
                            400000u
                            DEFAULT_ROUTE_PARAMS
                            []
                        |> ignore
                    )
                    ""

                let route2 =
                    graph.GetRoute
                        b
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

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
                            Some DEFAULT_AMOUNT_MSAT,
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
                            Some DEFAULT_AMOUNT_MSAT,
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

                let route1 =
                    gHigh.GetRoute
                        a
                        d
                        highAmount
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.isEmpty route1 ""

                let route2 =
                    gLow.GetRoute a d lowAmount 400000u DEFAULT_ROUTE_PARAMS []

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

                let route =
                    graph.GetRoute
                        a
                        a
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

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

                let route =
                    graph.GetRoute
                        a
                        b
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route) [ 1UL ] ""

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

                let route1 =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route1) [ 1UL; 2UL; 3UL; 4UL ] ""

                let route2 =
                    graph.GetRoute
                        e
                        a
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.isEmpty route2 ""

            testCase "calculate route and return metadata"
            <| fun _ ->
                let uab =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 1UL
                        Timestamp = 0u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 42L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2500L
                        FeeProportionalMillionths = 140u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let uba =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 1UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 43L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2501L
                        FeeProportionalMillionths = 141u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ubc =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 2UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 44L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2502L
                        FeeProportionalMillionths = 142u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ucb =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 2UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 45L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2503L
                        FeeProportionalMillionths = 143u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ucd =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 3UL
                        Timestamp = 1u
                        MessageFlags = 1uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 46L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2504L
                        FeeProportionalMillionths = 144u
                        HTLCMaximumMSat = Some(LNMoney.MilliSatoshis 500000000L)
                    }

                let udc =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 3UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 47L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2505L
                        FeeProportionalMillionths = 145u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ude =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 4UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 0uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 48L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2506L
                        FeeProportionalMillionths = 146u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let ued =
                    {
                        UnsignedChannelUpdateMsg.ChainHash =
                            Network.RegTest.GenesisHash
                        ShortChannelId = ShortChannelId.FromUInt64 4UL
                        Timestamp = 1u
                        MessageFlags = 0uy
                        ChannelFlags = 1uy
                        CLTVExpiryDelta = BlockHeightOffset16 1us
                        HTLCMinimumMSat = LNMoney.MilliSatoshis 49L
                        FeeBaseMSat = LNMoney.MilliSatoshis 2507L
                        FeeProportionalMillionths = 147u
                        HTLCMaximumMSat = Some DEFAULT_HTLC_MAXIMUM_MSAT
                    }

                let updates =
                    Map.empty
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 1UL
                             A = a
                             B = b
                         })
                        uab
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 1UL
                             A = b
                             B = a
                         })
                        uba
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 2UL
                             A = b
                             B = c
                         })
                        ubc
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 2UL
                             A = c
                             B = b
                         })
                        ucb
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 3UL
                             A = c
                             B = d
                         })
                        ucd
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 3UL
                             A = d
                             B = c
                         })
                        udc
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 4UL
                             A = d
                             B = e
                         })
                        ude
                    |> Map.add
                        ({
                             ChannelDesc.ShortChannelId =
                                 ShortChannelId.FromUInt64 4UL
                             A = e
                             B = d
                         })
                        ued

                let graph =
                    RoutingGraphData().Update
                        (updates |> Seq.map(fun pair -> pair.Key))
                        (updates
                         |> Seq.map(fun pair -> pair.Value)
                         |> makeUpdatesMap)
                        0u

                let hops =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                let expectedHops =
                    [
                        {
                            Source = a
                            Target = b
                            Update = uab
                            ShortChannelId = uab.ShortChannelId
                        }
                        {
                            Source = b
                            Target = c
                            Update = ubc
                            ShortChannelId = ubc.ShortChannelId
                        }
                        {
                            Source = c
                            Target = d
                            Update = ucd
                            ShortChannelId = ucd.ShortChannelId
                        }
                        {
                            Source = d
                            Target = e
                            Update = ude
                            ShortChannelId = ude.ShortChannelId
                        }
                    ]
                    |> List.map(fun x -> x :> IRoutingHopInfo)

                Expect.sequenceEqual hops expectedHops ""

            testCase "blacklist routes"
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

                let ignoredChannel = ShortChannelId.FromUInt64 3UL

                let graphWithBlacklist = graph.BlacklistChannel ignoredChannel

                let route1 =
                    graphWithBlacklist.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.isEmpty route1 ""

                // make sure we can find a route without the blacklist
                let route2 =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route2) [ 1UL; 2UL; 3UL; 4UL ] ""

            testCase
                "route to a destination that is not in the graph (with assisted routes)"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 10L,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 10L,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 10L,
                            10u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.isEmpty route "there should be no e node in the graph"

                // now we add the missing edge to reach the destination
                let extraDesc, extraUpdate =
                    makeUpdate(
                        4UL,
                        d,
                        e,
                        LNMoney.MilliSatoshis 5L,
                        5u,
                        None,
                        None,
                        Some(BlockHeightOffset16 1us)
                    )

                let extraGraphEdges =
                    [
                        [
                            ExtraHop.TryCreate(
                                extraDesc.A,
                                extraDesc.ShortChannelId,
                                extraUpdate.FeeBaseMSat,
                                extraUpdate.FeeProportionalMillionths,
                                extraUpdate.CLTVExpiryDelta
                            )
                            |> Result.deref
                        ]
                    ]

                let route1 =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        extraGraphEdges

                Expect.sequenceEqual (hops2Ids route1) [ 1UL; 2UL; 3UL; 4UL ] ""

            testCase "limit routes to 20 hops"
            <| fun () ->
                let nodes =
                    [
                        for _ in 0..22 -> (new Key()).PubKey |> NodeId
                    ]

                let descs, updates =
                    Seq.zip
                        (nodes |> List.rev |> List.skip 1 |> List.rev)
                        (nodes |> Seq.skip 1) // (0, 1) :: (1, 2) :: ...
                    |> Seq.mapi(fun i (na, nb) ->
                        makeUpdate(
                            uint64 i,
                            na,
                            nb,
                            LNMoney.MilliSatoshis 5,
                            0u,
                            None,
                            None,
                            None
                        )
                    )
                    |> Seq.toList
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let r18 =
                    graph.GetRoute
                        nodes.[0]
                        nodes.[18]
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual
                    (hops2Ids r18)
                    [ for i in 0..17 -> uint64 i ]
                    ""

                let r19 =
                    graph.GetRoute
                        nodes.[0]
                        nodes.[19]
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual
                    (hops2Ids r19)
                    [ for i in 0..18 -> uint64 i ]
                    ""

                let r20 =
                    graph.GetRoute
                        nodes.[0]
                        nodes.[20]
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual
                    (hops2Ids r20)
                    [ for i in 0..19 -> uint64 i ]
                    ""

                let r21 =
                    graph.GetRoute
                        nodes.[0]
                        nodes.[21]
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.isEmpty r21 ""

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
                            uint64 i,
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
                let descs2, updates2 =
                    (makeUpdate(
                        99UL,
                        nodes.[2],
                        nodes.[48],
                        LNMoney.MilliSatoshis 1000L,
                        0u,
                        None,
                        None,
                        None
                    ))
                    :: updates
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates2

                let graph = RoutingGraphData().Update descs2 updatesMap 0u

                let route =
                    graph.GetRoute
                        nodes.[0]
                        nodes.[49]
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual
                    (hops2Ids route)
                    [ 0UL; 1UL; 99UL; 48UL ]
                    ""

            testCase "ignore loops"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            a,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            d,
                            e,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route1 =
                    graph.GetRoute
                        a
                        e
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route1) [ 1UL; 2UL; 4UL; 5UL ] ""

            testCase
                "ensure the route calculation terminates correctly when selecting 0-fees edges"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 10,
                            10u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 10,
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
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route1 =
                    graph.GetRoute
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual (hops2Ids route1) [ 1UL; 3UL; 5UL ] ""

            testCase
                "ignore cheaper route when it has more than the requested CLTV limit"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 50us)
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 50us)
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 50us)
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis 5,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis 5,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        { DEFAULT_ROUTE_PARAMS with
                            RouteMaxCLTV = (BlockHeightOffset16 28us)
                        }
                        []

                Expect.sequenceEqual (hops2Ids route) [ 4UL; 5UL; 6UL ] ""

            testCase
                "ignore cheaper route when it grows longer than the requested size"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            4UL,
                            d,
                            e,
                            LNMoney.One,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.MilliSatoshis 5),
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            6UL,
                            b,
                            f,
                            LNMoney.One,
                            0u,
                            Some(LNMoney.MilliSatoshis 5),
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let route =
                    graph.GetRoute
                        a
                        f
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        { DEFAULT_ROUTE_PARAMS with
                            RouteMaxLength = 3
                        }
                        []

                Expect.sequenceEqual (hops2Ids route) [ 1UL; 6UL ] ""

            testCase "select a random route below the requested fee"
            <| fun _ ->
                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 1,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.MilliSatoshis 1,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 2,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 3,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis 3,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis 3,
                            0u,
                            None,
                            None,
                            None
                        )
                        makeUpdate(
                            7UL,
                            e,
                            c,
                            LNMoney.MilliSatoshis 9,
                            0u,
                            None,
                            None,
                            None
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let strictFeeParams =
                    { DEFAULT_ROUTE_PARAMS with
                        MaxFeeBase = LNMoney.MilliSatoshis 7
                        MaxFeePCT = 0.
                    }

                for _ in 0..10 do
                    let someRoute =
                        graph.GetRoute
                            a
                            d
                            DEFAULT_AMOUNT_MSAT
                            400000u
                            strictFeeParams
                            []

                    Expect.isNonEmpty someRoute ""

                    let routeCost =
                        totalRouteCost DEFAULT_AMOUNT_MSAT someRoute
                        - DEFAULT_AMOUNT_MSAT

                    let costMSat = routeCost.MilliSatoshi
                    Expect.isTrue (costMSat = 5L || costMSat = 6L) ""

            testCase "Use weight ratios to when computing the edge weight"
            <| fun _ ->
                let largeCap = LNMoney.MilliSatoshis 80000000000L

                let descs, updates =
                    [
                        makeUpdate(
                            1UL,
                            a,
                            b,
                            LNMoney.MilliSatoshis 0,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 13us)
                        )
                        makeUpdate(
                            4UL,
                            a,
                            e,
                            LNMoney.MilliSatoshis 0,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 12us)
                        )
                        makeUpdate(
                            2UL,
                            b,
                            c,
                            LNMoney.MilliSatoshis 1,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 500us)
                        )
                        makeUpdate(
                            3UL,
                            c,
                            d,
                            LNMoney.MilliSatoshis 1,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 500us)
                        )
                        makeUpdate(
                            5UL,
                            e,
                            f,
                            LNMoney.MilliSatoshis 2,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            6UL,
                            f,
                            d,
                            LNMoney.MilliSatoshis 2,
                            0u,
                            Some LNMoney.Zero,
                            None,
                            Some(BlockHeightOffset16 9us)
                        )
                        makeUpdate(
                            7UL,
                            e,
                            c,
                            LNMoney.MilliSatoshis 2,
                            0u,
                            Some LNMoney.Zero,
                            Some largeCap,
                            Some(BlockHeightOffset16 12us)
                        )
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let r =
                    graph.GetRoute
                        a
                        d
                        DEFAULT_AMOUNT_MSAT
                        400000u
                        DEFAULT_ROUTE_PARAMS
                        []

                Expect.sequenceEqual
                    (r |> Seq.map(fun hop -> hop.NodeId))
                    [ a; e; c ]
                    ""

                let routeClTVOptimized =
                    let p =
                        let r =
                            WeightRatios.TryCreate(1., 0., 0.) |> Result.deref

                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = r
                        }

                    graph.GetRoute a d DEFAULT_AMOUNT_MSAT 400000u p []

                Expect.sequenceEqual
                    (routeClTVOptimized |> Seq.map(fun hop -> hop.NodeId))
                    [ a; e; f ]
                    ""

                let routeCapOptimized =
                    let p =
                        let r =
                            WeightRatios.TryCreate(0., 0., 1.) |> Result.deref

                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = r
                        }

                    graph.GetRoute a d DEFAULT_AMOUNT_MSAT 400000u p []

                Expect.sequenceEqual
                    (routeCapOptimized |> Seq.map(fun hop -> hop.NodeId))
                    [ a; e; c ]
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
                        LNMoney.MilliSatoshis 1,
                        0u,
                        Some LNMoney.Zero,
                        None,
                        Some(BlockHeightOffset16 144us)
                    )

                let descs, updates =
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
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = wr
                        }

                    graph.GetRoute
                        a
                        d
                        (DEFAULT_AMOUNT_MSAT / 2)
                        currentBlockHeight
                        rp
                        []

                Expect.sequenceEqual
                    (routeScoreOptimized |> Seq.map(fun hop -> hop.NodeId))
                    [ a; b; c ]
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
                        Some LNMoney.Zero,
                        None,
                        Some(BlockHeightOffset16 cltv)
                    )

                let descs, updates =
                    [
                        mu(1UL, a, b, 12us)
                        mu(4UL, a, e, 12us)
                        mu(2UL, b, c, 10us) // smaller cltv
                        mu(3UL, c, d, 12us)
                        mu(5UL, e, f, 12us)
                        mu(6UL, f, d, 12us)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = wr
                        }

                    graph.GetRoute a d (DEFAULT_AMOUNT_MSAT / 2) 400000u rp []

                Expect.sequenceEqual
                    (routeScoreOptimized |> Seq.map(fun hop -> hop.NodeId))
                    [ a; b; c ]
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
                let descs, updates =
                    [
                        mu(1UL, a, b, 144us)
                        mu(4UL, a, e, 144us)
                        mu(2UL, b, c, 1000us)
                        mu(3UL, c, d, 900us)
                        mu(5UL, e, f, 144us)
                        mu(6UL, f, d, 144us)
                    ]
                    |> List.unzip

                let updatesMap = makeUpdatesMap updates

                let graph = RoutingGraphData().Update descs updatesMap 0u

                let routeScoreOptimized =
                    let wr =
                        WeightRatios.TryCreate(0.33, 0.33, 0.33) |> Result.deref

                    let rp =
                        { DEFAULT_ROUTE_PARAMS with
                            Ratios = wr
                        }

                    graph.GetRoute a d (DEFAULT_AMOUNT_MSAT / 2) 400000u rp []

                Expect.sequenceEqual
                    (routeScoreOptimized |> Seq.map(fun hop -> hop.NodeId))
                    [ a; e; f ]
                    ""
        ]
