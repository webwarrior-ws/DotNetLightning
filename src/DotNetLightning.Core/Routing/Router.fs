namespace DotNetLightning.Routing

open DotNetLightning.Utils.Primitives
open DotNetLightning.Utils

open DotNetLightning.Serialization.Msgs

open System
open DotNetLightning.Payment
open DotNetLightning.Routing.Graph
open NBitcoin

open QuikGraph
open QuikGraph.Algorithms

open ResultUtils
open ResultUtils.Portability

module Routing =

    /// This method is used after a payment failed, and we want to exclude some nodes that we know are failing
    let getIgnoredChannelDesc
        (channels: Map<ShortChannelId, PublicChannel>)
        (ignoredNodes: Set<NodeId>)
        =
        let desc =
            if ignoredNodes.IsEmpty then
                Seq.empty
            else
                channels
                |> Seq.map(fun kvp -> kvp.Value)
                |> Seq.filter(fun (channelData: PublicChannel) ->
                    ignoredNodes.Contains(channelData.Ann.NodeId1)
                    || ignoredNodes.Contains(channelData.Ann.NodeId2)
                )
                |> Seq.collect(fun pc ->
                    seq {
                        yield
                            {
                                ChannelDesc.ShortChannelId =
                                    pc.Ann.ShortChannelId
                                A = pc.Ann.NodeId1
                                B = pc.Ann.NodeId2
                            }

                        yield
                            {
                                ChannelDesc.ShortChannelId =
                                    pc.Ann.ShortChannelId
                                A = pc.Ann.NodeId2
                                B = pc.Ann.NodeId1
                            }
                    }
                )

        desc
    // ----- helpers -----
    /// BOLT11: "For each entry, the pubkey is the node ID of the start of the channel", and the last node is the destination
    /// The invoice doesn't explicitly specify the channel's htlcMaximumMsat, but we can safely assume that the channel
    /// should be able to route the payment, so we'll compute an htlcMaximumMSat accordingly.
    /// We could also get the channel capacity from the blockchain (since we have the shortChannelId) but that's more expensive
    /// We also need to make sure the channel isn't excluded by our heuristics.
    let internal toAssistedChannels
        (targetNode: NodeId)
        (amount: LNMoney)
        (extraRoute: seq<ExtraHop>)
        : seq<ShortChannelId * AssistedChannel> =
        let lastChannelCap =
            LNMoney.Max(amount, RoutingHeuristics.CAPACITY_CHANNEL_LOW)

        let nextNodeIds =
            seq {
                yield!
                    if (extraRoute |> Seq.isEmpty) then
                        Seq.empty
                    else
                        (extraRoute
                         |> Seq.map(fun x -> x.NodeIdValue)
                         |> Seq.skip 1)

                yield targetNode
            }

        extraRoute
        |> Seq.zip nextNodeIds
        |> Seq.rev
        |> Seq.fold
            (fun (amount: LNMoney, acs) (nextNodeId, extraHop) ->
                let nextAmount =
                    amount
                    + (Graph.EdgeWeightCaluculation.nodeFee
                        extraHop.FeeBaseValue
                        (int64 extraHop.FeeProportionalMillionthsValue)
                        amount)

                (nextAmount,
                 acs
                 |> Map.add
                     (extraHop.ShortChannelIdValue)
                     ({
                          AssistedChannel.ExtraHop = extraHop
                          NextNodeId = nextNodeId
                          HTLCMaximum = nextAmount
                      }))
            )
            (lastChannelCap, Map.empty)
        |> snd
        |> Map.toSeq

    /// Defined in BOLT7
    let ROUTE_MAX_LENGTH = 20
    /// Max allowed cltv for a route
    let DEFAULT_ROUTE_MAX_CLTV = BlockHeightOffset16(1008us)

    /// The default number of routes we'll search for when findRoute is called with randomize = true
    [<Literal>]
    let private DEFAULT_ROUTES_COUNT = 3

    /// Find a route in the graph between localNodeId and targetNodeId, returns the route.
    /// Will perform a k-shortest path selection given the @param numRoutes and randomly select one of the result
    let rec findRoute
        (g: RoutingGraph)
        (local: NodeId)
        (target: NodeId)
        (amount: LNMoney)
        (numRoutes: int)
        (extraE: IRoutingHopInfo list)
        (ignoredV: Set<NodeId>)
        (routeParams: RouteParams)
        (currentBlockHeight: BlockHeight)
        : Result<seq<ChannelHop>, RouterError> =

        if (local = target) then
            routeFindingError("Cannot route to yourself")
        else
            let feeBaseOk(fee: LNMoney) =
                fee <= routeParams.MaxFeeBase

            let feePctOk(fee: LNMoney, amount: LNMoney) =
                let f, a =
                    (fee.MilliSatoshi |> double),
                    (amount.MilliSatoshi |> double)

                let maxFee = (a) * routeParams.MaxFeePCT
                f <= maxFee

            let feeOk(f, a) =
                feeBaseOk(f) || feePctOk(f, a)

            let lengthOk(l: int) =
                let limit =
                    Math.Min(routeParams.RouteMaxLength, ROUTE_MAX_LENGTH)

                l <= limit

            let cltvOk(cltv: BlockHeightOffset16) =
                cltv <= routeParams.RouteMaxCLTV

            let candidates = 
                // make use of extraE !
                let tryGetPath = 
                    g.ShortestPathsDijkstra(
                        System.Func<RoutingGrpahEdge, float>(EdgeWeightCaluculation.edgeWeight amount), 
                        local)
                seq {
                    for i=1 to numRoutes do
                        match tryGetPath.Invoke target with
                        | true, path -> yield path
                        | false, _ -> ()
                }

            candidates
            |> Seq.toList
            |> function
                | [] -> routeFindingError "Route not found!"
                | routes ->
                    routes
                    |> if routeParams.Randomize then
                           (List.sortBy(fun _ -> Guid.NewGuid()))
                       else
                           id
                    |> List.head
                    |> fun x ->
                        (x |> Seq.map ChannelHop.FromGraphEdge) |> Ok

    let private toFakeUpdate
        (extraHop: ExtraHop)
        (htlcMaximum: LNMoney)
        : UnsignedChannelUpdateMsg =
        // the `direction` bit in flags will not be accurate but it doesn't matter because it is not used
        // what matters is that the `disable` bit is 0 so that this update doesn't get filtered out
        {
            UnsignedChannelUpdateMsg.ShortChannelId =
                extraHop.ShortChannelIdValue
            ChainHash = uint256.Zero
            Timestamp = DateTimeOffset.UtcNow.ToUnixTimeSeconds() |> uint32
            MessageFlags = 1uy
            ChannelFlags = 0uy
            CLTVExpiryDelta = extraHop.CLTVExpiryDeltaValue
            HTLCMinimumMSat = LNMoney.Zero
            FeeBaseMSat = extraHop.FeeBaseValue
            FeeProportionalMillionths = extraHop.FeeProportionalMillionthsValue
            HTLCMaximumMSat = Some(htlcMaximum)
        }
    // ----- ------
    let executeCommand (state: RouterState) (cmd: RouterCommand) =
        match state, cmd with
        | RouterState.Normal _d, (NetworkEvent(ChannelUpdateReceived _update)) ->
            failwith
                "Not implemented: Routing::executeCommand when state,cmd = Normal,NetworkEvent ChannelUpdateRecv"
        | RouterState.Normal d, (NetworkCommand(CalculateRoute routeRequest)) ->
            let {
                    Source = start
                    Target = t
                    Amount = a
                    AssistedRoutes = assistedRoutes
                    IgnoredNodes = ignoredV
                } =
                routeRequest

            let assistedChannels: Map<ShortChannelId, AssistedChannel> =
                assistedRoutes
                |> Seq.collect(toAssistedChannels t a)
                |> Map.ofSeq

            let extraEdges =
                assistedChannels
                |> Seq.map(fun kvp -> kvp.Value :> IRoutingHopInfo)
                |> Seq.toList

            let routeParams = routeRequest.RouteParams

            let routesToFind =
                if routeParams.Randomize then
                    DEFAULT_ROUTES_COUNT
                else
                    1

            findRoute
                (d.Graph)
                (start)
                t
                a
                routesToFind
                extraEdges
                ignoredV
                routeParams
                d.CurrentBlockHeight
        | _ ->
            failwith
                "Not implemented: Routing::executeCommand for some unknown state,cmd tuple"
