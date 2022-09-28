namespace DotNetLightning.Routing

open System

/// <namespacedoc>
///     <summary>
///         "DotNetLightning.Routing" contains a functions/types for calculating
///         the route for payment.
///         It is still WIP.
///     </summary>
/// </namespacedoc>
/// <exclude />
module NamespaceDocDummy =
    ()


open DotNetLightning.Utils
open DotNetLightning.Serialization.Msgs
open DotNetLightning.Payment

open QuikGraph
open QuikGraph.Algorithms
open QuikGraph.Algorithms.RankedShortestPath

open ResultUtils
open ResultUtils.Portability


type ChannelDesc =
    {
        ShortChannelId: ShortChannelId
        A: NodeId
        B: NodeId
    }


/// Information about hop in multi-hop payments
/// Used in edge cost calculation and onion packet creation.
/// Cannot reuse RoutingGrpahEdge because route can contain extra hops
/// through private channel (ExtraHop type)
type IRoutingHopInfo =
    abstract NodeId: NodeId
    abstract ShortChannelId: ShortChannelId
    abstract FeeBaseMSat: LNMoney
    abstract FeeProportionalMillionths: uint32
    abstract CltvExpiryDelta: uint32
    abstract HTLCMaximumMSat: LNMoney option
    abstract HTLCMinimumMSat: LNMoney


type RoutingGraphEdge =
    {
        Source: NodeId
        Target: NodeId
        ShortChannelId: ShortChannelId
        Update: UnsignedChannelUpdateMsg
    }

    interface IEdge<NodeId> with
        member this.Source = this.Source
        member this.Target = this.Target

    interface IRoutingHopInfo with
        override this.NodeId = this.Source
        override this.ShortChannelId = this.Update.ShortChannelId
        override this.FeeBaseMSat = this.Update.FeeBaseMSat

        override this.FeeProportionalMillionths =
            this.Update.FeeProportionalMillionths

        override this.CltvExpiryDelta =
            this.Update.CLTVExpiryDelta.Value |> uint32

        override this.HTLCMaximumMSat = this.Update.HTLCMaximumMSat
        override this.HTLCMinimumMSat = this.Update.HTLCMinimumMSat


type internal RoutingGraph = ArrayAdjacencyGraph<NodeId, RoutingGraphEdge>


module RoutingHeuristics =
    let BLOCK_TIME_TWO_MONTHS = 8640us |> BlockHeightOffset16
    let CAPACITY_CHANNEL_LOW = LNMoney.Satoshis 1000L

    let CAPACITY_CHANNEL_HIGH =
        DotNetLightning.Channel.ChannelConstants.MAX_FUNDING_SATOSHIS.Satoshi
        |> LNMoney.Satoshis

    [<Literal>]
    let CLTV_LOW = 9L

    [<Literal>]
    let CLTV_HIGH = 2016

    let normalize(v, min, max) : double =
        if (v <= min) then
            0.00001
        else if (v > max) then
            0.99999
        else
            (v - min) / (max - min)

    // factors?
    let CltvDeltaFactor = 1.0
    let CapacityFactor = 1.0


/// We use heuristics to calculate the weight of an edge based on channel age, cltv delta and capacity.
/// We favor older channels, with bigger capacity and small cltv delta
type WeightRatios =
    private
        {
            CLTVDeltaFactor: double
            AgeFactor: double
            CapacityFactor: double
        }

    static member TryCreate(cltvDeltaFactor, ageFactor, capacityFactor) =
        let s = cltvDeltaFactor + ageFactor + capacityFactor

        if (s <= 0. || 1. < s) then
            sprintf
                "sum of CLTVDeltaFactor + ageFactor + capacityFactor must in between 0 to 1. it was %f"
                s
            |> Error
        else
            {
                CLTVDeltaFactor = cltvDeltaFactor
                AgeFactor = ageFactor
                CapacityFactor = capacityFactor
            }
            |> Ok

    static member Default =
        {
            CLTVDeltaFactor = 0.333
            AgeFactor = 0.333
            CapacityFactor = 0.333
        }


type RouteParams =
    {
        Randomize: bool // not used
        MaxFeeBase: LNMoney
        MaxFeePCT: double
        RouteMaxLength: int
        RouteMaxCLTV: BlockHeightOffset16
        Ratios: WeightRatios
    }

    static member Default =
        {
            Randomize = false
            MaxFeeBase = LNMoney.MilliSatoshis(21000L)
            MaxFeePCT = 0.03
            RouteMaxLength = 20
            RouteMaxCLTV = BlockHeightOffset16 2160us
            Ratios = WeightRatios.Default
        }


module EdgeWeightCaluculation =
    let nodeFee
        (baseFee: LNMoney)
        (proportionalFee: int64)
        (paymentAmount: LNMoney)
        =
        baseFee
        + LNMoney.Satoshis(
            decimal(paymentAmount.Satoshi * proportionalFee) / 1000000.0m
        )

    let edgeFeeCost (amountWithFees: LNMoney) (edge: IRoutingHopInfo) =
        let result =
            nodeFee
                edge.FeeBaseMSat
                (int64 edge.FeeProportionalMillionths)
                amountWithFees
        // We can't have zero fee cost because it causes weight to be 0 regardless of expiry_delta
        LNMoney.Max(result, LNMoney.MilliSatoshis(1))

    /// Computes the weight for the given edge
    let edgeWeight
        (paymentAmount: LNMoney)
        (currentBlockHeight: uint32)
        (routeParams: RouteParams)
        (edge: IRoutingHopInfo)
        : float =
        let feeCost = float (edgeFeeCost paymentAmount edge).Value
        let channelCLTVDelta = edge.CltvExpiryDelta

        let edgeMaxCapacity =
            edge.HTLCMaximumMSat
            |> Option.defaultValue(RoutingHeuristics.CAPACITY_CHANNEL_LOW)

        if edgeMaxCapacity < paymentAmount then
            infinity // chanel capacity is too small, reject edge
        elif paymentAmount < edge.HTLCMinimumMSat then
            infinity // our payment is too small for the channel, reject edge
        else
            // Every edge is weighted by channel capacity, larger channels and less weight
            let capFactor =
                1.0
                - RoutingHeuristics.normalize(
                    float edgeMaxCapacity.MilliSatoshi,
                    float RoutingHeuristics.CAPACITY_CHANNEL_LOW.MilliSatoshi,
                    float RoutingHeuristics.CAPACITY_CHANNEL_HIGH.MilliSatoshi
                )

            // Every edge is weighted by cltv-delta value, normalized.
            let cltvFactor =
                RoutingHeuristics.normalize(
                    float channelCLTVDelta,
                    float RoutingHeuristics.CLTV_LOW,
                    float RoutingHeuristics.CLTV_HIGH
                )

            let channelBlockHeight = edge.ShortChannelId.BlockHeight.Value
            // every edge is weighted by funding block height where older blocks add less weight
            let ageFactor =
                RoutingHeuristics.normalize(
                    channelBlockHeight |> double,
                    (currentBlockHeight
                     - (uint32 RoutingHeuristics.BLOCK_TIME_TWO_MONTHS.Value))
                    |> double,
                    currentBlockHeight |> double
                )


            let factor =
                cltvFactor * routeParams.Ratios.CLTVDeltaFactor
                + capFactor * routeParams.Ratios.CapacityFactor
                + ageFactor * routeParams.Ratios.AgeFactor

            factor * feeCost


module ExtraHop =
    let internal toIRoutingHopInfo(extraHop: ExtraHop) =
        { new IRoutingHopInfo with
            override this.NodeId = extraHop.NodeIdValue
            override this.ShortChannelId = extraHop.ShortChannelIdValue
            override this.FeeBaseMSat = extraHop.FeeBaseValue

            override this.FeeProportionalMillionths =
                extraHop.FeeProportionalMillionthsValue

            override this.CltvExpiryDelta =
                extraHop.CLTVExpiryDeltaValue.Value |> uint32
            // Folowing values are only used in edge weight calculation
            override this.HTLCMaximumMSat =
                Some RoutingHeuristics.CAPACITY_CHANNEL_HIGH

            override this.HTLCMinimumMSat = LNMoney.Zero
        }


type ChannelUpdates =
    {
        Forward: UnsignedChannelUpdateMsg option
        Backward: UnsignedChannelUpdateMsg option
    }

    static member Empty =
        {
            Forward = None
            Backward = None
        }

    member this.With(update: UnsignedChannelUpdateMsg) =
        let isForward = (update.ChannelFlags &&& 1uy) = 0uy

        if isForward then
            match this.Forward with
            | Some(prevUpd) when update.Timestamp < prevUpd.Timestamp -> this
            | _ ->
                { this with
                    Forward = Some(update)
                }
        else
            match this.Backward with
            | Some(prevUpd) when update.Timestamp < prevUpd.Timestamp -> this
            | _ ->
                { this with
                    Backward = Some(update)
                }

    member this.Combine(other: ChannelUpdates) =
        let combine upd1opt upd2opt : UnsignedChannelUpdateMsg option =
            match upd1opt, upd2opt with
            | None, None -> None
            | Some(_), None -> upd1opt
            | None, Some(_) -> upd2opt
            | Some(upd1), Some(upd2) ->
                if upd1.Timestamp > upd2.Timestamp then
                    upd1opt
                else
                    upd2opt

        {
            Forward = combine this.Forward other.Forward
            Backward = combine this.Backward other.Backward
        }


type RoutingGraphData
    private
    (
        channelDescriptions: Set<ChannelDesc>,
        updates: Map<ShortChannelId, ChannelUpdates>,
        lastSyncTimestamp: uint32,
        blacklistedChannels: Set<ShortChannelId>,
        routingGraph: RoutingGraph
    ) =

    new() =
        RoutingGraphData(
            Set.empty,
            Map.empty,
            0u,
            Set.empty,
            RoutingGraph(AdjacencyGraph())
        )

    member this.LastSyncTimestamp = lastSyncTimestamp

    member this.Graph = routingGraph

    member this.Update
        (newChannelDescriptions: seq<ChannelDesc>)
        (newUpdates: Map<ShortChannelId, ChannelUpdates>)
        (syncTimestamp: uint32)
        : RoutingGraphData =
        let channelDescriptions =
            channelDescriptions
            |> Set.union(newChannelDescriptions |> Set.ofSeq)

        let updates =
            if updates.IsEmpty then
                newUpdates
            else
                let mutable tmpUpdates = updates

                newUpdates
                |> Map.iter(fun channelId newUpd ->
                    match tmpUpdates |> Map.tryFind channelId with
                    | Some upd ->
                        tmpUpdates <-
                            tmpUpdates |> Map.add channelId (upd.Combine newUpd)
                    | None ->
                        tmpUpdates <- tmpUpdates |> Map.add channelId newUpd
                )

                tmpUpdates

        let baseGraph = AdjacencyGraph<NodeId, RoutingGraphEdge>()

        for channelDesc in channelDescriptions do
            let updates = updates.[channelDesc.ShortChannelId]

            let addEdge source target (upd: UnsignedChannelUpdateMsg) =
                let edge =
                    {
                        Source = source
                        Target = target
                        ShortChannelId = upd.ShortChannelId
                        Update = upd
                    }

                baseGraph.AddVerticesAndEdge edge |> ignore

            updates.Forward |> Option.iter(addEdge channelDesc.A channelDesc.B)
            updates.Backward |> Option.iter(addEdge channelDesc.B channelDesc.A)

        RoutingGraphData(
            channelDescriptions,
            updates,
            syncTimestamp,
            blacklistedChannels,
            RoutingGraph(baseGraph)
        )

    member this.BlacklistChannel(shortChannelId: ShortChannelId) =
        let newBlacklistedChannels =
            blacklistedChannels |> Set.add shortChannelId

        let baseGraph = AdjacencyGraph<NodeId, RoutingGraphEdge>()

        baseGraph.AddVerticesAndEdgeRange(
            this.Graph.Edges
            |> Seq.filter(fun edge -> edge.ShortChannelId <> shortChannelId)
        )
        |> ignore

        RoutingGraphData(
            channelDescriptions,
            updates,
            this.LastSyncTimestamp,
            newBlacklistedChannels,
            RoutingGraph(baseGraph)
        )

    member this.GetChannelUpdates() =
        updates

    member private this.GetEdgeWeightFunction
        (paymentAmount: LNMoney)
        (currentBlockHeight: uint32)
        (routeParams: RouteParams)
        : System.Func<RoutingGraphEdge, float> =
        System.Func<RoutingGraphEdge, float>(
            EdgeWeightCaluculation.edgeWeight
                paymentAmount
                currentBlockHeight
                routeParams
        )

    member private this.IsRouteValid
        (routeParams: RouteParams)
        (paymentAmount: LNMoney)
        (route: seq<RoutingGraphEdge>)
        : bool =
        let maxRouteLength = min 20 routeParams.RouteMaxLength

        let totalFee =
            Seq.foldBack
                (fun edge acc ->
                    acc + EdgeWeightCaluculation.edgeFeeCost acc edge
                )
                route
                paymentAmount
            - paymentAmount

        let feePct =
            float(totalFee.MilliSatoshi) / float(paymentAmount.MilliSatoshi)

        Seq.length route <= maxRouteLength
        && (route |> Seq.sumBy(fun edge -> edge.Update.CLTVExpiryDelta))
           <= routeParams.RouteMaxCLTV
        && (totalFee <= routeParams.MaxFeeBase
            || feePct <= routeParams.MaxFeePCT)

    /// Use Hoffman-Pavley K shortest paths algorithm to find valid route
    member private this.FallbackGetRoute
        (sourceNodeId: NodeId)
        (targetNodeId: NodeId)
        (paymentAmount: LNMoney)
        (currentBlockHeight: uint32)
        (routeParams: RouteParams)
        =
        let hoffmanPavleyAlgorithm =
            HoffmanPavleyRankedShortestPathAlgorithm(
                routingGraph.ToBidirectionalGraph(),
                this.GetEdgeWeightFunction
                    paymentAmount
                    currentBlockHeight
                    routeParams
            )

        hoffmanPavleyAlgorithm.SetRootVertex sourceNodeId
        hoffmanPavleyAlgorithm.SetTargetVertex targetNodeId
        hoffmanPavleyAlgorithm.ShortestPathCount <- 100 // should be enough?

        hoffmanPavleyAlgorithm.Compute()

        hoffmanPavleyAlgorithm.ComputedShortestPaths
        |> Seq.filter(this.IsRouteValid routeParams paymentAmount)
        |> Seq.tryHead
        |> Option.defaultValue Seq.empty
        |> Seq.cast<IRoutingHopInfo>
        |> Seq.toArray

    /// Get shortest route from source to target node taking cahnnel fees and cltv expiry deltas into account.
    /// Don't use channels that have insufficient capacity for given paymentAmount.
    /// See EdgeWeightCaluculation.edgeWeight.
    /// extraRoutes is [optional] list of extra routes (see PaymentRequest.RoutingInfo and BOLT11)
    /// If no routes can be found, return empty sequence.
    member this.GetRoute
        (sourceNodeId: NodeId)
        (targetNodeId: NodeId)
        (paymentAmount: LNMoney)
        (currentBlockHeight: uint32)
        (routeParams: RouteParams)
        (extraRoutes: ExtraHop list list)
        : seq<IRoutingHopInfo> =
        let tryGetPath =
            routingGraph.ShortestPathsDijkstra(
                this.GetEdgeWeightFunction
                    paymentAmount
                    currentBlockHeight
                    routeParams,
                sourceNodeId
            )

        let directRoute: IRoutingHopInfo [] =
            match tryGetPath.Invoke targetNodeId with
            | true, path when this.IsRouteValid routeParams paymentAmount path ->
                path |> Seq.cast<IRoutingHopInfo> |> Seq.toArray
            | true, _ ->
                this.FallbackGetRoute
                    sourceNodeId
                    targetNodeId
                    paymentAmount
                    currentBlockHeight
                    routeParams
            | false, _ -> Array.empty

        if Array.isEmpty directRoute then
            seq {
                for extraRoute in extraRoutes do
                    match extraRoute with
                    | head :: _ ->
                        let publicPart =
                            this.GetRoute
                                sourceNodeId
                                head.NodeIdValue
                                paymentAmount
                                currentBlockHeight
                                routeParams
                                []
                            |> Seq.cast<IRoutingHopInfo>
                            |> Seq.toArray

                        if not <| Array.isEmpty publicPart then
                            let extraPart =
                                extraRoute
                                |> Seq.map ExtraHop.toIRoutingHopInfo
                                |> Seq.toArray

                            yield Array.append publicPart extraPart
                    | _ -> ()
            }
            |> Seq.sortBy(fun route ->
                route
                |> Array.sumBy(fun hopInfo ->
                    EdgeWeightCaluculation.edgeWeight
                        paymentAmount
                        currentBlockHeight
                        routeParams
                        hopInfo
                )
            )
            |> Seq.tryHead
            |> Option.defaultValue [||]
            :> seq<IRoutingHopInfo>
        else
            directRoute :> seq<IRoutingHopInfo>
