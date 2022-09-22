namespace DotNetLightning.Routing

open System

/// <namespacedoc>
///     <summary>
///         "DotNetLightning.Routing" contains a functions/types for calculating
///         the route for payment. and to track the routing information.
///         It is still WIP.
///     </summary>
/// </namespacedoc>
/// <exclude />
module NamespaceDocDummy =
    ()

open System.Collections.Generic
open DotNetLightning.Utils
open DotNetLightning.Serialization.Msgs
open NBitcoin

open QuikGraph
open QuikGraph.Algorithms

open ResultUtils
open ResultUtils.Portability


module Graph =
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
    
    type ChannelDesc =
        {
            ShortChannelId: ShortChannelId
            A: NodeId
            B: NodeId
        }

    type PublicChannel =
        private
            {
                Announcement: UnsignedChannelAnnouncementMsg
                FundingTxId: TxId
                Capacity: Money
                Update1Opt: option<UnsignedChannelUpdateMsg>
                Update2Opt: option<UnsignedChannelUpdateMsg>
            }

        member this.Ann = this.Announcement

        static member Create(a, fundingTxId, cap, u1, u2) =
            {
                Announcement = a
                FundingTxId = fundingTxId
                Capacity = cap
                Update1Opt = u1
                Update2Opt = u2
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


    type RoutingGrpahEdge = 
        {
            Source : NodeId
            Target : NodeId
            ShortChannelId : ShortChannelId
            Update: UnsignedChannelUpdateMsg
        }
        interface IEdge<NodeId> with
            member this.Source = this.Source
            member this.Target = this.Target

        interface IRoutingHopInfo with
            override self.NodeId = self.Source
            override self.ShortChannelId = self.Update.ShortChannelId
            override self.FeeBaseMSat = self.Update.FeeBaseMSat
            override self.FeeProportionalMillionths = self.Update.FeeProportionalMillionths
            override self.CltvExpiryDelta = self.Update.CLTVExpiryDelta.Value |> uint32
            override self.HTLCMaximumMSat = self.Update.HTLCMaximumMSat
            override self.HTLCMinimumMSat = self.Update.HTLCMinimumMSat


    type RoutingGraph = ArrayAdjacencyGraph<NodeId, RoutingGrpahEdge>


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


    module EdgeWeightCaluculation =
        let nodeFee (baseFee: LNMoney) (proportionalFee: int64) (paymentAmount: LNMoney) =
            baseFee + LNMoney.Satoshis(decimal(paymentAmount.Satoshi * proportionalFee) / 1000000.0m)
        
        let edgeFeeCost (amountWithFees: LNMoney) (edge: IRoutingHopInfo) =
            let result =
                nodeFee
                    edge.FeeBaseMSat 
                    (int64 edge.FeeProportionalMillionths)
                    amountWithFees
            // We can't have zero fee cost because it causes weight to be 0 regardless of expiry_delta
            LNMoney.Max(result, LNMoney.MilliSatoshis(1))

        /// Computes the weight for the given edge
        let edgeWeight (paymentAmount: LNMoney) (edge: IRoutingHopInfo) : float =
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
                let capFactor =
                    1.0 - RoutingHeuristics.normalize(
                            float edgeMaxCapacity.MilliSatoshi,
                            float RoutingHeuristics.CAPACITY_CHANNEL_LOW.MilliSatoshi,
                            float RoutingHeuristics.CAPACITY_CHANNEL_HIGH.MilliSatoshi)
                let cltvFactor =
                    RoutingHeuristics.normalize(
                        float channelCLTVDelta,
                        float RoutingHeuristics.CLTV_LOW,
                        float RoutingHeuristics.CLTV_HIGH)
                let factor = 
                    cltvFactor * RoutingHeuristics.CltvDeltaFactor 
                    + capFactor * RoutingHeuristics.CapacityFactor
                factor * feeCost


    type ChannelUpdates =
        {
            Forward: UnsignedChannelUpdateMsg option
            Backward: UnsignedChannelUpdateMsg option
        }
        static member Empty = { Forward = None; Backward = None }
    
        member self.With(update: UnsignedChannelUpdateMsg) =
            let isForward = (update.ChannelFlags &&& 1uy) = 0uy
            if isForward then
                match self.Forward with
                | Some(prevUpd) when update.Timestamp < prevUpd.Timestamp -> self
                | _ -> { self with Forward = Some(update) }
            else
                match self.Backward with
                | Some(prevUpd) when update.Timestamp < prevUpd.Timestamp -> self
                | _ -> { self with Backward = Some(update) }

        member self.Combine(other: ChannelUpdates) =
            let combine upd1opt upd2opt : UnsignedChannelUpdateMsg option =
                match upd1opt, upd2opt with
                | None, None -> None
                | Some(_), None -> upd1opt
                | None, Some(_) -> upd2opt
                | Some(upd1), Some(upd2) -> if upd1.Timestamp > upd2.Timestamp then upd1opt else upd2opt
            { Forward = combine self.Forward other.Forward; Backward = combine self.Backward other.Backward }


    type RoutingGraphData private(announcements: Set<UnsignedChannelAnnouncementMsg>, 
                                  updates: Map<ShortChannelId, ChannelUpdates>,
                                  lastSyncTimestamp: uint32,
                                  blacklistedChannels: Set<ShortChannelId>,
                                  routingGraph: RoutingGraph) =
        
        new() = RoutingGraphData(Set.empty, Map.empty, 0u, Set.empty, RoutingGraph(AdjacencyGraph()))

        member self.LastSyncTimestamp = lastSyncTimestamp

        member self.Graph = routingGraph

        member self.Update (newAnnouncements : seq<UnsignedChannelAnnouncementMsg>) 
                            (newUpdates: Map<ShortChannelId, ChannelUpdates>) 
                            (syncTimestamp: uint32) : RoutingGraphData =
            let announcements = 
                announcements 
                |> Set.union (newAnnouncements |> Set.ofSeq)
                |> Set.filter (fun ann -> not (blacklistedChannels |> Set.contains ann.ShortChannelId))
            
            let updates =
                if updates.IsEmpty then
                    newUpdates
                else
                    let mutable tmpUpdates = updates
                    newUpdates |> Map.iter (fun channelId newUpd ->
                        match tmpUpdates |> Map.tryFind channelId with
                        | Some upd ->
                            tmpUpdates <- tmpUpdates |> Map.add channelId (upd.Combine newUpd)
                        | None ->
                            tmpUpdates <- tmpUpdates |> Map.add channelId newUpd )
                    tmpUpdates

            let baseGraph = AdjacencyGraph<NodeId, RoutingGrpahEdge>()

            for ann in announcements do
                let updates = updates.[ann.ShortChannelId]
                    
                let addEdge source target (upd : UnsignedChannelUpdateMsg) =
                    let edge = { Source = source; Target = target; ShortChannelId = upd.ShortChannelId; Update = upd }
                    baseGraph.AddVerticesAndEdge edge |> ignore
                
                updates.Forward |> Option.iter (addEdge ann.NodeId1 ann.NodeId2)
                updates.Backward |> Option.iter (addEdge ann.NodeId2 ann.NodeId1)

            RoutingGraphData(announcements, updates, syncTimestamp, blacklistedChannels, RoutingGraph(baseGraph))

        member self.BlacklistChannel(shortChannelId: ShortChannelId) =
            let newBlacklistedChannels = blacklistedChannels |> Set.add shortChannelId
            let baseGraph = AdjacencyGraph<NodeId, RoutingGrpahEdge>()
            baseGraph.AddVerticesAndEdgeRange(
                self.Graph.Edges |> Seq.filter (fun edge ->  edge.ShortChannelId <> shortChannelId))
                |> ignore
            RoutingGraphData(announcements, updates, self.LastSyncTimestamp, newBlacklistedChannels, RoutingGraph(baseGraph))

        member self.GetChannelUpdates() =
            updates
