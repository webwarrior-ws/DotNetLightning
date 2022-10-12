namespace rec DotNetLightning.Serialization.Msgs

open System
open System.IO
open System.Runtime.CompilerServices
open System.Linq

open NBitcoin

open DotNetLightning.Utils
open DotNetLightning.Utils.Primitives
open DotNetLightning.Utils.OnionError
open DotNetLightning.Core.Utils.Extensions

open DotNetLightning.Serialization

open ResultUtils
open ResultUtils.Portability

// todo: generate dtos automatically from the spec when the tooling is ready (e.g. https://github.com/ElementsProject/lightning/blob/master/tools/generate-wire.py)

/// <namespacedoc>
///     <summary>
///         This namespace contains a p2p messages for lightning network.
///     </summary>
/// </namespacedoc>
/// <exclude />
module NamespaceDocDummy =
    ()

type P2PDecodeError =
    | UnknownVersion
    | FeatureError of FeatureError
    | InvalidValue
    | ExtraAddressesPerType
    | BadLengthDescriptor
    | UnexpectedEndOfStream of EndOfStreamException
    | IO of IOException

    member this.Message =
        match this with
        | UnknownVersion -> "Unknown version"
        | FeatureError featureError ->
            sprintf "Feature error: %s" featureError.Message
        | InvalidValue -> "Invalid value"
        | ExtraAddressesPerType -> "Extra address per type"
        | BadLengthDescriptor -> "Bad length descriptor"
        | UnexpectedEndOfStream endOfStreamException ->
            sprintf
                "Unexpected end of stream: %s"
                (endOfStreamException.Message)
        | IO ioException -> sprintf "IO error: %s" ioException.Message

type UnknownVersionException(msg) =
    inherit FormatException(msg)

module internal TypeFlag =
    [<Literal>]
    let Init = 16us

    [<Literal>]
    let Error = 17us

    [<Literal>]
    let Warning = 1us

    [<Literal>]
    let Ping = 18us

    [<Literal>]
    let Pong = 19us

    [<Literal>]
    let OpenChannel = 32us

    [<Literal>]
    let AcceptChannel = 33us

    [<Literal>]
    let FundingCreated = 34us

    [<Literal>]
    let FundingSigned = 35us

    [<Literal>]
    let FundingLocked = 36us

    [<Literal>]
    let Shutdown = 38us

    [<Literal>]
    let ClosingSigned = 39us

    [<Literal>]
    let UpdateAddHTLC = 128us

    [<Literal>]
    let UpdateFulfillHTLC = 130us

    [<Literal>]
    let UpdateFailHTLC = 131us

    [<Literal>]
    let UpdateFailMalformedHTLC = 135us

    [<Literal>]
    let ChannelReestablish = 136us

    [<Literal>]
    let CommitmentSigned = 132us

    [<Literal>]
    let RevokeAndACK = 133us

    [<Literal>]
    let UpdateFee = 134us

    [<Literal>]
    let AnnouncementSignatures = 259us

    [<Literal>]
    let ChannelAnnouncement = 256us

    [<Literal>]
    let NodeAnnouncement = 257us

    [<Literal>]
    let ChannelUpdate = 258us

    [<Literal>]
    let QueryShortChannelIds = 261us

    [<Literal>]
    let ReplyShortChannelIdsEnd = 262us

    [<Literal>]
    let QueryChannelRange = 263us

    [<Literal>]
    let ReplyChannelRange = 264us

    [<Literal>]
    let GossipTimestampFilter = 265us

/// The marker interface to annotate the type for p2p serialization.
type ILightningMsg =
    interface
    end

/// The marker interface to annotate the type for very basic p2p messaging.
/// e.g. ping/pong, error.
type ISetupMsg =
    inherit ILightningMsg

/// The marker interface to annotate the type p2p messages for managing the
/// channel itself e.g. opening/closure/update.
/// but not for htlc payment.
type IChannelMsg =
    inherit ILightningMsg

/// The marker interface to annotate the p2p message related to HTLC update.
type IHTLCMsg =
    inherit IChannelMsg

/// The marker interface to annotate the p2p message related to channel update
/// (including htlc creation/revocation).
type IUpdateMsg =
    inherit IChannelMsg

/// The marker interface to annotate the p2p message related to routing
type IRoutingMsg =
    inherit ILightningMsg

/// The marker interface to annotate the p2p message related to querying
/// the information to other nodes.
type IQueryMsg =
    inherit IRoutingMsg

/// The type serializable for lightning p2p network.
/// Should throw `FormatException` when it fails.
type ILightningSerializable<'T when 'T :> ILightningSerializable<'T>> =
    abstract Deserialize: LightningReaderStream -> 'T
    abstract Serialize: LightningWriterStream -> unit

module ILightningSerializable =
    let internal getDummyInstance<'T when 'T: (new: unit -> 'T) and 'T :> ILightningSerializable<'T>>
        ()
        =
        new 'T()

    let internal fromBytes<'T when 'T: (new: unit -> 'T) and 'T :> ILightningSerializable<'T>>
        (data: array<byte>)
        =
        use ms = new MemoryStream(data)
        use ls = new LightningReaderStream(ms)
        let instance: 'T = getDummyInstance()
        instance.Deserialize ls

    let internal deserialize<'T when 'T: (new: unit -> 'T) and 'T :> ILightningSerializable<'T>>
        (ls: LightningReaderStream)
        =
        let instance: 'T = getDummyInstance()
        instance.Deserialize ls

    let internal deserializeWithFlag
        (ls: LightningReaderStream)
        : ILightningMsg =
        let t = ls.ReadUInt16(false)

        match t with
        | TypeFlag.Init -> deserialize<InitMsg>(ls) :> ILightningMsg
        | TypeFlag.Error -> deserialize<ErrorMsg>(ls) :> ILightningMsg
        | TypeFlag.Warning -> deserialize<WarningMsg>(ls) :> ILightningMsg
        | TypeFlag.Ping -> deserialize<PingMsg>(ls) :> ILightningMsg
        | TypeFlag.Pong -> deserialize<PongMsg>(ls) :> ILightningMsg
        | TypeFlag.OpenChannel ->
            deserialize<OpenChannelMsg>(ls) :> ILightningMsg
        | TypeFlag.AcceptChannel ->
            deserialize<AcceptChannelMsg>(ls) :> ILightningMsg
        | TypeFlag.FundingCreated ->
            deserialize<FundingCreatedMsg>(ls) :> ILightningMsg
        | TypeFlag.FundingSigned ->
            deserialize<FundingSignedMsg>(ls) :> ILightningMsg
        | TypeFlag.FundingLocked ->
            deserialize<FundingLockedMsg>(ls) :> ILightningMsg
        | TypeFlag.Shutdown -> deserialize<ShutdownMsg>(ls) :> ILightningMsg
        | TypeFlag.ClosingSigned ->
            deserialize<ClosingSignedMsg>(ls) :> ILightningMsg
        | TypeFlag.UpdateAddHTLC ->
            deserialize<UpdateAddHTLCMsg>(ls) :> ILightningMsg
        | TypeFlag.UpdateFulfillHTLC ->
            deserialize<UpdateFulfillHTLCMsg>(ls) :> ILightningMsg
        | TypeFlag.UpdateFailHTLC ->
            deserialize<UpdateFailHTLCMsg>(ls) :> ILightningMsg
        | TypeFlag.UpdateFailMalformedHTLC ->
            deserialize<UpdateFailMalformedHTLCMsg>(ls) :> ILightningMsg
        | TypeFlag.ChannelReestablish ->
            deserialize<ChannelReestablishMsg>(ls) :> ILightningMsg
        | TypeFlag.CommitmentSigned ->
            deserialize<CommitmentSignedMsg>(ls) :> ILightningMsg
        | TypeFlag.RevokeAndACK ->
            deserialize<RevokeAndACKMsg>(ls) :> ILightningMsg
        | TypeFlag.UpdateFee -> deserialize<UpdateFeeMsg>(ls) :> ILightningMsg
        | TypeFlag.AnnouncementSignatures ->
            deserialize<AnnouncementSignaturesMsg>(ls) :> ILightningMsg
        | TypeFlag.ChannelAnnouncement ->
            deserialize<ChannelAnnouncementMsg>(ls) :> ILightningMsg
        | TypeFlag.NodeAnnouncement ->
            deserialize<NodeAnnouncementMsg>(ls) :> ILightningMsg
        | TypeFlag.ChannelUpdate ->
            deserialize<ChannelUpdateMsg>(ls) :> ILightningMsg
        | TypeFlag.QueryShortChannelIds ->
            deserialize<QueryShortChannelIdsMsg>(ls) :> ILightningMsg
        | TypeFlag.ReplyShortChannelIdsEnd ->
            deserialize<ReplyShortChannelIdsEndMsg>(ls) :> ILightningMsg
        | TypeFlag.QueryChannelRange ->
            deserialize<QueryChannelRangeMsg>(ls) :> ILightningMsg
        | TypeFlag.ReplyChannelRange ->
            deserialize<ReplyChannelRangeMsg>(ls) :> ILightningMsg
        | TypeFlag.GossipTimestampFilter ->
            deserialize<GossipTimestampFilterMsg>(ls) :> ILightningMsg
        | x -> raise <| FormatException(sprintf "Unknown message type %i" x)

    let serializeWithFlags (ls: LightningWriterStream) (data: ILightningMsg) =
        match data with
        | :? InitMsg as d ->
            ls.Write(TypeFlag.Init, false)

            (d :> ILightningSerializable<InitMsg>)
                .Serialize(ls)
        | :? ErrorMsg as d ->
            ls.Write(TypeFlag.Error, false)

            (d :> ILightningSerializable<ErrorMsg>)
                .Serialize(ls)
        | :? WarningMsg as warningMsg ->
            ls.Write(TypeFlag.Warning, false)

            (warningMsg :> ILightningSerializable<WarningMsg>)
                .Serialize ls
        | :? PingMsg as d ->
            ls.Write(TypeFlag.Ping, false)

            (d :> ILightningSerializable<PingMsg>)
                .Serialize(ls)
        | :? PongMsg as d ->
            ls.Write(TypeFlag.Pong, false)

            (d :> ILightningSerializable<PongMsg>)
                .Serialize(ls)
        | :? OpenChannelMsg as d ->
            ls.Write(TypeFlag.OpenChannel, false)

            (d :> ILightningSerializable<OpenChannelMsg>)
                .Serialize(ls)
        | :? AcceptChannelMsg as d ->
            ls.Write(TypeFlag.AcceptChannel, false)

            (d :> ILightningSerializable<AcceptChannelMsg>)
                .Serialize(ls)
        | :? FundingCreatedMsg as d ->
            ls.Write(TypeFlag.FundingCreated, false)

            (d :> ILightningSerializable<FundingCreatedMsg>)
                .Serialize(ls)
        | :? FundingSignedMsg as d ->
            ls.Write(TypeFlag.FundingSigned, false)

            (d :> ILightningSerializable<FundingSignedMsg>)
                .Serialize(ls)
        | :? FundingLockedMsg as d ->
            ls.Write(TypeFlag.FundingLocked, false)

            (d :> ILightningSerializable<FundingLockedMsg>)
                .Serialize(ls)
        | :? ShutdownMsg as d ->
            ls.Write(TypeFlag.Shutdown, false)

            (d :> ILightningSerializable<ShutdownMsg>)
                .Serialize(ls)
        | :? ClosingSignedMsg as d ->
            ls.Write(TypeFlag.ClosingSigned, false)

            (d :> ILightningSerializable<ClosingSignedMsg>)
                .Serialize(ls)
        | :? UpdateAddHTLCMsg as d ->
            ls.Write(TypeFlag.UpdateAddHTLC, false)

            (d :> ILightningSerializable<UpdateAddHTLCMsg>)
                .Serialize(ls)
        | :? UpdateFulfillHTLCMsg as d ->
            ls.Write(TypeFlag.UpdateFulfillHTLC, false)

            (d :> ILightningSerializable<UpdateFulfillHTLCMsg>)
                .Serialize(ls)
        | :? UpdateFailHTLCMsg as d ->
            ls.Write(TypeFlag.UpdateFailHTLC, false)

            (d :> ILightningSerializable<UpdateFailHTLCMsg>)
                .Serialize(ls)
        | :? UpdateFailMalformedHTLCMsg as d ->
            ls.Write(TypeFlag.UpdateFailMalformedHTLC, false)

            (d :> ILightningSerializable<UpdateFailMalformedHTLCMsg>)
                .Serialize(ls)
        | :? ChannelReestablishMsg as d ->
            ls.Write(TypeFlag.ChannelReestablish, false)

            (d :> ILightningSerializable<ChannelReestablishMsg>)
                .Serialize(ls)
        | :? CommitmentSignedMsg as d ->
            ls.Write(TypeFlag.CommitmentSigned, false)

            (d :> ILightningSerializable<CommitmentSignedMsg>)
                .Serialize(ls)
        | :? RevokeAndACKMsg as d ->
            ls.Write(TypeFlag.RevokeAndACK, false)

            (d :> ILightningSerializable<RevokeAndACKMsg>)
                .Serialize(ls)
        | :? UpdateFeeMsg as d ->
            ls.Write(TypeFlag.UpdateFee, false)

            (d :> ILightningSerializable<UpdateFeeMsg>)
                .Serialize(ls)
        | :? AnnouncementSignaturesMsg as d ->
            ls.Write(TypeFlag.AnnouncementSignatures, false)

            (d :> ILightningSerializable<AnnouncementSignaturesMsg>)
                .Serialize(ls)
        | :? ChannelAnnouncementMsg as d ->
            ls.Write(TypeFlag.ChannelAnnouncement, false)

            (d :> ILightningSerializable<ChannelAnnouncementMsg>)
                .Serialize(ls)
        | :? NodeAnnouncementMsg as d ->
            ls.Write(TypeFlag.NodeAnnouncement, false)

            (d :> ILightningSerializable<NodeAnnouncementMsg>)
                .Serialize(ls)
        | :? ChannelUpdateMsg as d ->
            ls.Write(TypeFlag.ChannelUpdate, false)

            (d :> ILightningSerializable<ChannelUpdateMsg>)
                .Serialize(ls)
        | :? QueryShortChannelIdsMsg as d ->
            ls.Write(TypeFlag.QueryShortChannelIds, false)

            (d :> ILightningSerializable<QueryShortChannelIdsMsg>)
                .Serialize(ls)
        | :? ReplyShortChannelIdsEndMsg as d ->
            ls.Write(TypeFlag.ReplyShortChannelIdsEnd, false)

            (d :> ILightningSerializable<ReplyShortChannelIdsEndMsg>)
                .Serialize(ls)
        | :? QueryChannelRangeMsg as d ->
            ls.Write(TypeFlag.QueryChannelRange, false)

            (d :> ILightningSerializable<QueryChannelRangeMsg>)
                .Serialize(ls)
        | :? ReplyChannelRangeMsg as d ->
            ls.Write(TypeFlag.ReplyChannelRange, false)

            (d :> ILightningSerializable<ReplyChannelRangeMsg>)
                .Serialize(ls)
        | :? GossipTimestampFilterMsg as d ->
            ls.Write(TypeFlag.GossipTimestampFilter, false)

            (d :> ILightningSerializable<GossipTimestampFilterMsg>)
                .Serialize(ls)
        | x ->
            failwithf
                "%A is not known lightning message. This should never happen"
                x

/// Functions to work with LightningMsg
module LightningMsg =
    let fromBytes<'T when 'T :> ILightningMsg>
        (b: array<byte>)
        : Result<_, P2PDecodeError> =
        try
            use ms = new MemoryStream(b)
            use ls = new LightningReaderStream(ms)
            ILightningSerializable.deserializeWithFlag ls |> Ok
        with
        | :? EndOfStreamException as ex -> UnexpectedEndOfStream ex |> Error
        | :? System.IO.IOException as ex -> P2PDecodeError.IO ex |> Error

/// Extension methods for `ILightningMsg`
[<Extension>]
type ILightningMsgExtension() =
    [<Extension>]
    static member ToBytes(this: ILightningMsg) =
        use ms = new MemoryStream()
        use ls = new LightningWriterStream(ms)
        ILightningSerializable.serializeWithFlags ls this
        ms.ToArray()

/// Extension methods for `ILightningSerializable`
[<Extension>]
type ILightningSerializableExtension() =
    [<Extension>]
    static member ToBytes(this: ILightningSerializable<'T>) =
        use ms = new MemoryStream()
        use ls = new LightningWriterStream(ms)
        this.Serialize(ls)
        ms.ToArray()

    [<Extension>]
    static member SerializeWithLen
        (
            this: ILightningSerializable<'T>,
            w: LightningWriterStream
        ) =
        let d = this.ToBytes()
        w.WriteWithLen(d)

    [<Extension>]
    static member ToBytesWithLen(this: ILightningSerializable<'T>) =
        let d = this.ToBytes()
        use ms = new MemoryStream()
        use ls = new LightningWriterStream(ms)
        ls.WriteWithLen(d)
        ms.ToArray()

    [<Extension>]
    static member Clone(this: ILightningSerializable<'T>) =
        ILightningSerializable.fromBytes<'T>(this.ToBytes())


// ---------- network message primitives
/// Before TLV gets standardized. Optional fields are defined directly
/// in bolt.
/// This a type annotation to make clear that the field is such an optional
/// type. The actual type is just a standard `FSharpOption`.
type OptionalField<'T> = option<'T>

/// onion_packet described in [bolt04](https://github.com/lightning/bolts/blob/master/04-onion-routing.md)
/// todo: add methods to parse `OnionPayload` from `HopData` field.
[<CLIMutable; StructuralComparison; StructuralEquality>]
type OnionPacket =
    {
        Version: uint8
        /// This might be 33 bytes of 0uy in case of last packet
        /// So we are not using `PubKey` to represent pubkey
        PublicKey: array<byte>
        HopData: array<byte>
        HMAC: uint256
    }

    static member LastPacket =
        {
            Version = 0uy
            PublicKey = Array.zeroCreate 33
            HopData = Array.zeroCreate 1300
            HMAC = uint256.Zero
        }

    member this.IsLastPacket = this.HMAC = uint256.Zero

    interface ILightningSerializable<OnionPacket> with
        member this.Deserialize(ls: LightningReaderStream) =
            {
                Version =
                    let v = ls.ReadUInt8()

                    if (v <> 0uy) then
                        raise
                        <| UnknownVersionException(
                            "Unknown version byte for OnionPacket"
                        )
                    else
                        v

                PublicKey = ls.ReadBytes(33)
                HopData = ls.ReadBytes(1300)
                HMAC = ls.ReadUInt256(true)
            }

        member this.Serialize ls =
            ls.Write(this.Version)
            ls.Write(this.PublicKey)
            ls.Write(this.HopData)
            ls.Write(this.HMAC, true)

type OnionErrorPacket =
    {
        Data: array<byte>
    }

/// `init` in [bolt01](https://github.com/lightning/bolts/blob/master/01-messaging.md)
[<CLIMutable>]
type InitMsg =
    {
        Features: FeatureBits
        TLVStream: array<InitTLV>
    }

    interface ISetupMsg

    interface ILightningSerializable<InitMsg> with
        member this.Deserialize(ls: LightningReaderStream) =
            // For backwards compatibility reason, we must consider legacy
            // `global features` section. (see bolt 1)
            let globalFeatures = ls.ReadWithLen()
            let localFeatures = ls.ReadWithLen()

            let oredFeatures =
                let len = Math.Max(globalFeatures.Length, localFeatures.Length)
                let oredFeatures = Array.zeroCreate len

                for index in 0 .. (len - 1) do
                    let globalFeaturesByte =
                        if index < globalFeatures.Length then
                            globalFeatures.[globalFeatures.Length - 1 - index]
                        else
                            0uy

                    let localFeaturesByte =
                        if index < localFeatures.Length then
                            localFeatures.[localFeatures.Length - 1 - index]
                        else
                            0uy

                    oredFeatures.[len - 1 - index] <-
                        globalFeaturesByte ||| localFeaturesByte

                oredFeatures

            {
                Features = oredFeatures |> FeatureBits.CreateUnsafe
                TLVStream =
                    ls.ReadTLVStream() |> Array.map(InitTLV.FromGenericTLV)
            }

        member this.Serialize ls =
            // For legacy compatiblity we treat the VariableLengthOnion feature specially.
            // Older versions of the lightning protocol spec had a
            // distinction between global and local features, of which
            // VariableLengthOnion was the only global feature. Although
            // this distinction has since been removed, older clients still
            // expect VariableLengthOnion to appear in the global_features
            // field of an init message and other features to appear only
            // in the local_features field. This is still compatible with
            // newer clients since those clients simply OR the two feature fields.
            let localFeatures = this.Features.ToByteArray()

            let globalFeatures =
                let mandatory =
                    this.Features.HasFeature(
                        Feature.VariableLengthOnion,
                        FeaturesSupport.Mandatory
                    )

                let optional =
                    this.Features.HasFeature(
                        Feature.VariableLengthOnion,
                        FeaturesSupport.Optional
                    )

                let globalFeatures =
                    let zero = FeatureBits.Zero

                    if mandatory then
                        zero.SetFeature
                            Feature.VariableLengthOnion
                            FeaturesSupport.Mandatory
                            true
                    elif optional then
                        zero.SetFeature
                            Feature.VariableLengthOnion
                            FeaturesSupport.Optional
                            true
                    else
                        zero

                globalFeatures.ToByteArray()

            ls.WriteWithLen(globalFeatures)
            ls.WriteWithLen(localFeatures)

            ls.WriteTLVStream(
                this.TLVStream |> Array.map(fun tlv -> tlv.ToGenericTLV())
            )

/// `ping` in [bolt01](https://github.com/lightning/bolts/blob/master/01-messaging.md)
[<CLIMutable>]
type PingMsg =
    {
        PongLen: uint16
        BytesLen: uint16
    }

    interface ISetupMsg

    interface ILightningSerializable<PingMsg> with
        member this.Deserialize ls =
            let result =
                {
                    PongLen = ls.ReadUInt16(false)
                    BytesLen = ls.ReadUInt16(false)
                }

            ls.ReadBytes(int32 this.BytesLen) |> ignore
            result

        member this.Serialize ls =
            ls.Write(this.PongLen, false)
            ls.Write(this.BytesLen, false)
            ls.Write(Array.zeroCreate<byte>((int) this.BytesLen))

/// `pong` in [bolt01](https://github.com/lightning/bolts/blob/master/01-messaging.md)
[<CLIMutable>]
type PongMsg =
    {
        BytesLen: uint16
    }

    interface ISetupMsg

    interface ILightningSerializable<PongMsg> with
        member this.Deserialize ls =
            let result =
                {
                    BytesLen = ls.ReadUInt16(false)
                }

            ls.ReadBytes(int32 this.BytesLen) |> ignore
            result

        member this.Serialize ls =
            ls.Write(this.BytesLen, false)
            ls.Write(Array.zeroCreate<byte>((int) this.BytesLen))

/// `open_channel` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type OpenChannelMsg =
    {
        Chainhash: uint256
        TemporaryChannelId: ChannelId
        FundingSatoshis: Money
        PushMSat: LNMoney
        DustLimitSatoshis: Money
        MaxHTLCValueInFlightMsat: LNMoney
        ChannelReserveSatoshis: Money
        HTLCMinimumMsat: LNMoney
        FeeRatePerKw: FeeRatePerKw
        ToSelfDelay: BlockHeightOffset16
        MaxAcceptedHTLCs: uint16
        FundingPubKey: FundingPubKey
        RevocationBasepoint: RevocationBasepoint
        PaymentBasepoint: PaymentBasepoint
        DelayedPaymentBasepoint: DelayedPaymentBasepoint
        HTLCBasepoint: HtlcBasepoint
        FirstPerCommitmentPoint: PerCommitmentPoint
        ChannelFlags: ChannelFlags
        TLVs: array<OpenChannelTLV>
    }

    interface IChannelMsg

    interface ILightningSerializable<OpenChannelMsg> with
        member this.Deserialize ls =
            {
                Chainhash = ls.ReadUInt256(true)
                TemporaryChannelId = ChannelId(ls.ReadUInt256(true))
                FundingSatoshis = Money.Satoshis(ls.ReadUInt64(false))
                PushMSat = LNMoney.MilliSatoshis(ls.ReadUInt64(false))
                DustLimitSatoshis = Money.Satoshis(ls.ReadUInt64(false))

                MaxHTLCValueInFlightMsat =
                    LNMoney.MilliSatoshis(ls.ReadInt64(false))

                ChannelReserveSatoshis = Money.Satoshis(ls.ReadInt64(false))
                HTLCMinimumMsat = LNMoney.MilliSatoshis(ls.ReadInt64(false))
                FeeRatePerKw = FeeRatePerKw(ls.ReadUInt32(false))
                ToSelfDelay = BlockHeightOffset16(ls.ReadUInt16(false))
                MaxAcceptedHTLCs = ls.ReadUInt16(false)
                FundingPubKey = ls.ReadFundingPubKey()
                RevocationBasepoint = ls.ReadRevocationBasepoint()
                PaymentBasepoint = ls.ReadPaymentBasepoint()
                DelayedPaymentBasepoint = ls.ReadDelayedPaymentBasepoint()
                HTLCBasepoint = ls.ReadHtlcBasepoint()
                FirstPerCommitmentPoint = ls.ReadPerCommitmentPoint()
                ChannelFlags = ls.ReadChannelFlags()

                TLVs =
                    ls.ReadTLVStream()
                    |> Array.map OpenChannelTLV.FromGenericTLV
            }

        member this.Serialize ls =
            ls.Write(this.Chainhash, true)
            ls.Write(this.TemporaryChannelId.Value, true)
            ls.Write(this.FundingSatoshis.Satoshi, false)
            ls.Write(this.PushMSat.MilliSatoshi, false)
            ls.Write(this.DustLimitSatoshis.Satoshi, false)
            ls.Write(this.MaxHTLCValueInFlightMsat.MilliSatoshi, false)
            ls.Write(this.ChannelReserveSatoshis.Satoshi, false)
            ls.Write(this.HTLCMinimumMsat.MilliSatoshi, false)
            ls.Write(this.FeeRatePerKw.Value, false)
            ls.Write(this.ToSelfDelay.Value, false)
            ls.Write(this.MaxAcceptedHTLCs, false)
            ls.Write(this.FundingPubKey.ToBytes())
            ls.Write(this.RevocationBasepoint.ToBytes())
            ls.Write(this.PaymentBasepoint.ToBytes())
            ls.Write(this.DelayedPaymentBasepoint.ToBytes())
            ls.Write(this.HTLCBasepoint.ToBytes())
            ls.Write(this.FirstPerCommitmentPoint.ToBytes())
            ls.Write(this.ChannelFlags.IntoUInt8())

            this.TLVs
            |> Array.map(fun tlv -> tlv.ToGenericTLV())
            |> ls.WriteTLVStream

    member this.ShutdownScriptPubKey() : Option<ShutdownScriptPubKey> =
        Seq.choose
            (function
            | OpenChannelTLV.UpfrontShutdownScript script -> Some script
            | _ -> None)
            this.TLVs
        |> Seq.tryExactlyOne
        |> Option.flatten

/// `accept_channel` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type AcceptChannelMsg =
    {
        TemporaryChannelId: ChannelId
        DustLimitSatoshis: Money
        MaxHTLCValueInFlightMsat: LNMoney
        ChannelReserveSatoshis: Money
        HTLCMinimumMSat: LNMoney
        MinimumDepth: BlockHeightOffset32
        ToSelfDelay: BlockHeightOffset16
        MaxAcceptedHTLCs: uint16
        FundingPubKey: FundingPubKey
        RevocationBasepoint: RevocationBasepoint
        PaymentBasepoint: PaymentBasepoint
        DelayedPaymentBasepoint: DelayedPaymentBasepoint
        HTLCBasepoint: HtlcBasepoint
        FirstPerCommitmentPoint: PerCommitmentPoint
        TLVs: array<AcceptChannelTLV>
    }

    interface IChannelMsg

    interface ILightningSerializable<AcceptChannelMsg> with
        member this.Deserialize ls =
            {
                TemporaryChannelId = ChannelId(ls.ReadUInt256(true))
                DustLimitSatoshis = ls.ReadUInt64(false) |> Money.Satoshis

                MaxHTLCValueInFlightMsat =
                    ls.ReadUInt64(false) |> LNMoney.MilliSatoshis

                ChannelReserveSatoshis = ls.ReadUInt64(false) |> Money.Satoshis

                HTLCMinimumMSat = ls.ReadUInt64(false) |> LNMoney.MilliSatoshis

                MinimumDepth = ls.ReadUInt32(false) |> BlockHeightOffset32
                ToSelfDelay = ls.ReadUInt16(false) |> BlockHeightOffset16
                MaxAcceptedHTLCs = ls.ReadUInt16(false)
                FundingPubKey = ls.ReadFundingPubKey()
                RevocationBasepoint = ls.ReadRevocationBasepoint()
                PaymentBasepoint = ls.ReadPaymentBasepoint()
                DelayedPaymentBasepoint = ls.ReadDelayedPaymentBasepoint()
                HTLCBasepoint = ls.ReadHtlcBasepoint()
                FirstPerCommitmentPoint = ls.ReadPerCommitmentPoint()

                TLVs =
                    ls.ReadTLVStream()
                    |> Array.map AcceptChannelTLV.FromGenericTLV
            }

        member this.Serialize ls =
            ls.Write(this.TemporaryChannelId.Value.ToBytes())
            ls.Write(this.DustLimitSatoshis.Satoshi, false)
            ls.Write(this.MaxHTLCValueInFlightMsat.MilliSatoshi, false)
            ls.Write(this.ChannelReserveSatoshis.Satoshi, false)
            ls.Write(this.HTLCMinimumMSat.MilliSatoshi, false)
            ls.Write(this.MinimumDepth.Value, false)
            ls.Write(this.ToSelfDelay.Value, false)
            ls.Write(this.MaxAcceptedHTLCs, false)
            ls.Write(this.FundingPubKey.ToBytes())
            ls.Write(this.RevocationBasepoint.ToBytes())
            ls.Write(this.PaymentBasepoint.ToBytes())
            ls.Write(this.DelayedPaymentBasepoint.ToBytes())
            ls.Write(this.HTLCBasepoint.ToBytes())
            ls.Write(this.FirstPerCommitmentPoint.ToBytes())

            this.TLVs
            |> Array.map(fun tlv -> tlv.ToGenericTLV())
            |> ls.WriteTLVStream

    member this.ShutdownScriptPubKey() : Option<ShutdownScriptPubKey> =
        Seq.choose
            (function
            | AcceptChannelTLV.UpfrontShutdownScript script -> Some script
            | _ -> None)
            this.TLVs
        |> Seq.tryExactlyOne
        |> Option.flatten

/// `funding_created` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type FundingCreatedMsg =
    {
        TemporaryChannelId: ChannelId
        FundingTxId: TxId
        FundingOutputIndex: TxOutIndex
        Signature: LNECDSASignature
    }

    interface IChannelMsg

    interface ILightningSerializable<FundingCreatedMsg> with
        member this.Deserialize ls =
            {
                TemporaryChannelId = ls.ReadUInt256(true) |> ChannelId
                FundingTxId = ls.ReadUInt256(true) |> TxId
                FundingOutputIndex = ls.ReadUInt16(false) |> TxOutIndex
                Signature = ls.ReadECDSACompact()
            }

        member this.Serialize ls =
            ls.Write(this.TemporaryChannelId.Value.ToBytes())
            ls.Write(this.FundingTxId.Value.ToBytes())
            ls.Write(this.FundingOutputIndex.Value, false)
            ls.Write(this.Signature)

/// `funding_signed` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type FundingSignedMsg =
    {
        ChannelId: ChannelId
        Signature: LNECDSASignature
    }

    interface IChannelMsg

    interface ILightningSerializable<FundingSignedMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ChannelId(ls.ReadUInt256(true))
                Signature = ls.ReadECDSACompact()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.Signature)

/// `funding_locked` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type FundingLockedMsg =
    {
        ChannelId: ChannelId
        NextPerCommitmentPoint: PerCommitmentPoint
    }

    interface IChannelMsg

    interface ILightningSerializable<FundingLockedMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                NextPerCommitmentPoint = ls.ReadPerCommitmentPoint()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.NextPerCommitmentPoint.ToBytes())

/// `shutdown` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type ShutdownMsg =
    {
        ChannelId: ChannelId
        ScriptPubKey: ShutdownScriptPubKey
    }

    interface IChannelMsg

    interface ILightningSerializable<ShutdownMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                ScriptPubKey = ls.ReadShutdownScriptPubKey()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.WriteWithLen(this.ScriptPubKey.ToBytes())

/// `closing_signed` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type ClosingSignedMsg =
    {
        ChannelId: ChannelId
        FeeSatoshis: Money
        Signature: LNECDSASignature
    }

    interface IChannelMsg

    interface ILightningSerializable<ClosingSignedMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                FeeSatoshis = ls.ReadUInt64(false) |> Money.Satoshis
                Signature = ls.ReadECDSACompact()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.FeeSatoshis.Satoshi, false)
            ls.Write(this.Signature)

/// `update_add_htlc` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable; StructuralComparison; StructuralEquality>]
type UpdateAddHTLCMsg =
    {
        ChannelId: ChannelId
        HTLCId: HTLCId
        Amount: LNMoney
        PaymentHash: PaymentHash
        CLTVExpiry: BlockHeight
        OnionRoutingPacket: OnionPacket
    }

    interface IHTLCMsg
    interface IUpdateMsg

    interface ILightningSerializable<UpdateAddHTLCMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                HTLCId = ls.ReadUInt64(false) |> HTLCId
                Amount = ls.ReadUInt64(false) |> LNMoney.MilliSatoshis
                PaymentHash = ls.ReadUInt256(false) |> PaymentHash
                CLTVExpiry = ls.ReadUInt32(false) |> BlockHeight

                OnionRoutingPacket =
                    ILightningSerializable.deserialize<OnionPacket>(ls)
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.HTLCId.Value, false)
            ls.Write(this.Amount.MilliSatoshi, false)
            ls.Write(this.PaymentHash.ToBytes())
            ls.Write(this.CLTVExpiry.Value, false)

            (this.OnionRoutingPacket :> ILightningSerializable<OnionPacket>)
                .Serialize(ls)

/// `update_fulfill_htlc` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type UpdateFulfillHTLCMsg =
    {
        ChannelId: ChannelId
        HTLCId: HTLCId
        PaymentPreimage: PaymentPreimage
    }

    interface IHTLCMsg
    interface IUpdateMsg

    interface ILightningSerializable<UpdateFulfillHTLCMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                HTLCId = ls.ReadUInt64(false) |> HTLCId

                PaymentPreimage =
                    ls.ReadBytes PaymentPreimage.LENGTH
                    |> PaymentPreimage.Create
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.HTLCId.Value, false)
            ls.Write(this.PaymentPreimage.ToByteArray())

/// `update_fail_htlc` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type UpdateFailHTLCMsg =
    {
        ChannelId: ChannelId
        HTLCId: HTLCId
        Reason: OnionErrorPacket
    }

    interface IHTLCMsg
    interface IUpdateMsg

    interface ILightningSerializable<UpdateFailHTLCMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                HTLCId = ls.ReadUInt64(false) |> HTLCId

                Reason =
                    {
                        Data = ls.ReadWithLen()
                    }
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.HTLCId.Value, false)
            ls.WriteWithLen(this.Reason.Data)

/// `update_fail_malformed_htlc` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type UpdateFailMalformedHTLCMsg =
    {
        ChannelId: ChannelId
        HTLCId: HTLCId
        Sha256OfOnion: uint256
        FailureCode: FailureCode
    }

    interface IHTLCMsg
    interface IUpdateMsg

    interface ILightningSerializable<UpdateFailMalformedHTLCMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                HTLCId = ls.ReadUInt64(false) |> HTLCId
                Sha256OfOnion = ls.ReadUInt256(true)
                FailureCode = ls.ReadUInt16(false) |> OnionError.FailureCode
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.HTLCId.Value, false)
            ls.Write(this.Sha256OfOnion, true)
            ls.Write(this.FailureCode.Value, false)

/// `commitment_signed` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type CommitmentSignedMsg =
    {
        ChannelId: ChannelId
        Signature: LNECDSASignature
        HTLCSignatures: list<LNECDSASignature>
    }

    interface IHTLCMsg

    interface ILightningSerializable<CommitmentSignedMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                Signature = ls.ReadECDSACompact()

                HTLCSignatures =
                    let len = ls.ReadUInt16(false)
                    [ 1us .. len ] |> List.map(fun _ -> ls.ReadECDSACompact())
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.Signature)
            ls.Write((uint16) this.HTLCSignatures.Length, false)
            this.HTLCSignatures |> List.iter(ls.Write)

/// `revoke_and_ack` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type RevokeAndACKMsg =
    {
        ChannelId: ChannelId
        PerCommitmentSecret: PerCommitmentSecret
        NextPerCommitmentPoint: PerCommitmentPoint
    }

    interface IHTLCMsg

    interface ILightningSerializable<RevokeAndACKMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                PerCommitmentSecret = ls.ReadPerCommitmentSecret()
                NextPerCommitmentPoint = ls.ReadPerCommitmentPoint()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.PerCommitmentSecret.ToBytes())
            ls.Write(this.NextPerCommitmentPoint.ToBytes())

/// `update_fee` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type UpdateFeeMsg =
    {
        ChannelId: ChannelId
        FeeRatePerKw: FeeRatePerKw
    }

    interface IChannelMsg
    interface IUpdateMsg

    interface ILightningSerializable<UpdateFeeMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                FeeRatePerKw = ls.ReadUInt32(false) |> FeeRatePerKw
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.FeeRatePerKw.Value, false)

/// `data_loss_protect` in `channel_reestablish` which exists only when
/// `option_data_lock_protect` is negotiated
/// see [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type DataLossProtect =
    {
        YourLastPerCommitmentSecret: Option<PerCommitmentSecret>
        MyCurrentPerCommitmentPoint: PerCommitmentPoint
    }

    interface ILightningSerializable<DataLossProtect> with
        member this.Deserialize(ls: LightningReaderStream) =
            {
                YourLastPerCommitmentSecret =
                    let bytes = ls.ReadBytes PerCommitmentSecret.BytesLength

                    if bytes.All(fun b -> b = 0uy) then
                        None
                    else
                        Some <| PerCommitmentSecret.FromBytes bytes

                MyCurrentPerCommitmentPoint = ls.ReadPerCommitmentPoint()
            }

        member this.Serialize(ls: LightningWriterStream) : unit =
            match this.YourLastPerCommitmentSecret with
            | Some perCommitmentSecret ->
                ls.Write(perCommitmentSecret.ToBytes())
            | None -> ls.Write(Array.zeroCreate PerCommitmentSecret.BytesLength)

            ls.Write(this.MyCurrentPerCommitmentPoint.ToBytes())


/// `channel_reestablish` in [bolt02](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md)
[<CLIMutable>]
type ChannelReestablishMsg =
    {
        ChannelId: ChannelId
        NextCommitmentNumber: CommitmentNumber
        NextRevocationNumber: CommitmentNumber
        DataLossProtect: OptionalField<DataLossProtect>
    }

    interface IChannelMsg

    interface ILightningSerializable<ChannelReestablishMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId
                NextCommitmentNumber = ls.ReadCommitmentNumber()
                NextRevocationNumber = ls.ReadCommitmentNumber()

                DataLossProtect =
                    ls.TryReadAll()
                    |> Option.map
                        ILightningSerializable.fromBytes<DataLossProtect>
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write this.NextCommitmentNumber
            ls.Write this.NextRevocationNumber

            match this.DataLossProtect with
            | None -> ()
            | Some dataLossProtect ->
                (dataLossProtect :> ILightningSerializable<DataLossProtect>)
                    .Serialize ls

/// `announcement_signatures` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type AnnouncementSignaturesMsg =
    {
        ChannelId: ChannelId
        ShortChannelId: ShortChannelId
        NodeSignature: LNECDSASignature
        BitcoinSignature: LNECDSASignature
    }

    interface IRoutingMsg

    interface ILightningSerializable<AnnouncementSignaturesMsg> with
        member this.Deserialize ls =
            {
                ChannelId = ls.ReadUInt256(true) |> ChannelId

                ShortChannelId =
                    ls.ReadUInt64(false) |> ShortChannelId.FromUInt64

                NodeSignature = ls.ReadECDSACompact()
                BitcoinSignature = ls.ReadECDSACompact()
            }

        member this.Serialize ls =
            ls.Write(this.ChannelId.Value.ToBytes())
            ls.Write(this.ShortChannelId)
            ls.Write(this.NodeSignature)
            ls.Write(this.BitcoinSignature)

/// ip address for Lightning Node's p2p connection.
type NetAddress =
    | IPv4 of IPv4Or6Data
    | IPv6 of IPv4Or6Data
    | OnionV2 of OnionV2EndPoint
    | OnionV3 of OnionV3EndPoint
    | DnsHostName of DnsHostName

    member this.GetId() =
        match this with
        | IPv4 _ -> 1uy
        | IPv6 _ -> 2uy
        | OnionV2 _ -> 3uy
        | OnionV3 _ -> 4uy
        | DnsHostName _ -> 5uy

    member this.Length =
        match this with
        | IPv4 _ -> 6us
        | IPv6 _ -> 18us
        | OnionV2 _ -> 12us
        | OnionV3 _ -> 37us
        | DnsHostName {
                          HostName = name
                      } -> name.Length |> uint16

    member this.WriteTo(ls: LightningWriterStream) =
        ls.Write(this.GetId())

        match this with
        | IPv4 d ->
            ls.Write(d.Addr)
            ls.Write(d.Port, false)
        | IPv6 d ->
            ls.Write(d.Addr)
            ls.Write(d.Port, false)
        | OnionV2 d ->
            ls.Write(d.Addr)
            ls.Write(d.Port, false)
        | OnionV3 d ->
            ls.Write(d.Ed25519PubKey)
            ls.Write(d.CheckSum, false)
            ls.Write(d.Version)
            ls.Write(d.Port, false)
        | DnsHostName d ->
            ls.WriteByte(d.HostName.Length |> uint8)
            ls.Write(d.HostName)
            ls.Write(d.Port, false)

    static member ReadFrom
        (ls: LightningReaderStream)
        : NetAddrSerializationResult =
        let id = ls.ReadUInt8()

        match id with
        | 1uy ->
            let addr = ls.ReadBytes(4)
            let port = ls.ReadUInt16(false)

            IPv4
                {
                    Addr = addr
                    Port = port
                }
            |> Ok
        | 2uy ->
            let addr = ls.ReadBytes(16)
            let port = ls.ReadUInt16((false))

            IPv6
                {
                    Addr = addr
                    Port = port
                }
            |> Ok
        | 3uy ->
            let addr = ls.ReadBytes(10)
            let port = ls.ReadUInt16(false)

            OnionV2
                {
                    Addr = addr
                    Port = port
                }
            |> Ok
        | 4uy ->
            let ed25519PK = ls.ReadBytes(32)
            let checkSum = ls.ReadUInt16(false)
            let v = ls.ReadUInt8()
            let port = ls.ReadUInt16(false)

            OnionV3
                {
                    OnionV3EndPoint.Ed25519PubKey = ed25519PK
                    CheckSum = checkSum
                    Version = v
                    Port = port
                }
            |> Ok
        | 5uy ->
            let hostnameLength = ls.ReadByte()
            let hostname = ls.ReadBytes(int hostnameLength)
            let port = ls.ReadUInt16(false)

            DnsHostName
                {
                    HostName = hostname
                    Port = port
                }
            |> Ok
        | unknown -> Result.Error(unknown)

/// Pair of Address and port.
and IPv4Or6Data =
    {
        /// 4 byte in case of IPv4. 16 byes in case of IPv6
        Addr: array<byte>
        Port: uint16
    }

/// Pair of Address and port.
and OnionV2EndPoint =
    {
        /// 10 bytes
        Addr: array<byte>
        Port: uint16
    }

/// Onion address v3 contains information more than v2 or normal ipv4/v6 address
/// e.g. Checksum and the version number.
and OnionV3EndPoint =
    {
        Ed25519PubKey: array<byte>
        CheckSum: uint16
        Version: uint8
        Port: uint16
    }

and DnsHostName =
    {
        HostName: byte []
        Port: uint16
    }

and NetAddrSerializationResult = Result<NetAddress, UnknownNetAddr>
and UnknownNetAddr = byte



/// `node_announcement` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
/// without signatures.
/// Features are stored as byte array because node_announcement with invalid or unknown features
/// should not raise exception on deserialization. They can be accessed using Features property
[<CLIMutable>]
type UnsignedNodeAnnouncementMsg =
    {
        FeatureBitsArray: array<byte>
        Timestamp: uint32
        NodeId: NodeId
        RGB: RGB
        Alias: uint256
        Addresses: array<NetAddress>
        ExcessAddressData: array<byte>
        ExcessData: array<byte>
    }

    member this.Features: Result<FeatureBits, FeatureError> =
        this.FeatureBitsArray |> FeatureBits.TryCreate

    interface ILightningSerializable<UnsignedNodeAnnouncementMsg> with
        member this.Deserialize ls =
            let featureBitsArray = ls.ReadWithLen()
            let timestamp = ls.ReadUInt32(false)
            let nodeId = ls.ReadPubKey() |> NodeId
            let rgb = ls.ReadRGB()
            let alias = ls.ReadUInt256(true)
            let addrLen = ls.ReadUInt16(false)
            let mutable addresses: list<NetAddress> = []
            let mutable addrReadPos = 0us
            let mutable foundUnknown = false
            let mutable excessAddressDataByte = 0uy

            let messageAddresses =
                while addrReadPos < addrLen && (not foundUnknown) do
                    let addr = NetAddress.ReadFrom ls

                    match addr with
                    | Error v ->
                        excessAddressDataByte <- v
                        foundUnknown <- true
                        addrReadPos <- addrReadPos + 1us
                    | Ok addr ->
                        addrReadPos <- addrReadPos + (1us + addr.Length)
                        addresses <- addr :: addresses

                addresses |> List.rev |> Array.ofList

            let excessAddressData =
                if addrReadPos < addrLen then
                    if foundUnknown then
                        Array.append
                            [| excessAddressDataByte |]
                            (ls.ReadBytes(int(addrLen - addrReadPos)))
                    else
                        (ls.ReadBytes(int(addrLen - addrReadPos)))
                else if foundUnknown then
                    [| excessAddressDataByte |]
                else
                    [||]

            {
                FeatureBitsArray = featureBitsArray
                Timestamp = timestamp
                NodeId = nodeId
                RGB = rgb
                Alias = alias
                Addresses = messageAddresses
                ExcessAddressData = excessAddressData
                ExcessData =
                    match ls.TryReadAll() with
                    | Some b -> b
                    | None -> [||]
            }

        member this.Serialize ls =
            ls.WriteWithLen(this.FeatureBitsArray)
            ls.Write(this.Timestamp, false)
            ls.Write(this.NodeId.Value)
            ls.Write(this.RGB)
            ls.Write(this.Alias, true)

            let mutable addrLen: uint16 =
                (this.Addresses |> Array.sumBy(fun addr -> addr.Length + 1us)) // 1 byte for type field

            let excessAddrLen = (uint16 this.ExcessAddressData.Length)
            addrLen <- excessAddrLen + addrLen
            ls.Write(addrLen, false)
            this.Addresses |> Array.iter(fun addr -> addr.WriteTo(ls))
            ls.Write(this.ExcessAddressData)
            ls.Write(this.ExcessData)

/// `node_announcement` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type NodeAnnouncementMsg =
    {
        Signature: LNECDSASignature
        Contents: UnsignedNodeAnnouncementMsg
    }

    interface IRoutingMsg

    interface ILightningSerializable<NodeAnnouncementMsg> with
        member this.Deserialize ls =
            {
                Signature = ls.ReadECDSACompact()

                Contents =
                    ILightningSerializable.deserialize<UnsignedNodeAnnouncementMsg>(
                        ls
                    )
            }

        member this.Serialize ls =
            ls.Write(this.Signature)

            (this.Contents
            :> ILightningSerializable<UnsignedNodeAnnouncementMsg>)
                .Serialize(ls)


/// `channel_announcement` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
/// without signatures
[<StructuralComparison; StructuralEquality; CLIMutable>]
type UnsignedChannelAnnouncementMsg =
    {
        Features: FeatureBits
        ChainHash: uint256
        ShortChannelId: ShortChannelId
        NodeId1: NodeId
        NodeId2: NodeId
        BitcoinKey1: ComparablePubKey
        BitcoinKey2: ComparablePubKey
        ExcessData: array<byte>
    }

    interface ILightningSerializable<UnsignedChannelAnnouncementMsg> with
        member this.Deserialize ls =
            {
                Features = ls.ReadWithLen() |> FeatureBits.CreateUnsafe
                ChainHash = ls.ReadUInt256(true)

                ShortChannelId =
                    ls.ReadUInt64(false) |> ShortChannelId.FromUInt64

                NodeId1 = ls.ReadPubKey() |> NodeId
                NodeId2 = ls.ReadPubKey() |> NodeId
                BitcoinKey1 = ls.ReadPubKey() |> ComparablePubKey
                BitcoinKey2 = ls.ReadPubKey() |> ComparablePubKey

                ExcessData =
                    match ls.TryReadAll() with
                    | Some b -> b
                    | None -> [||]
            }

        member this.Serialize ls =
            ls.WriteWithLen(this.Features.ToByteArray())
            ls.Write(this.ChainHash, true)
            ls.Write(this.ShortChannelId)
            ls.Write(this.NodeId1.Value)
            ls.Write(this.NodeId2.Value)
            ls.Write(this.BitcoinKey1.Value)
            ls.Write(this.BitcoinKey2.Value)
            ls.Write(this.ExcessData)

/// `channel_announcement` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type ChannelAnnouncementMsg =
    {
        NodeSignature1: LNECDSASignature
        NodeSignature2: LNECDSASignature
        BitcoinSignature1: LNECDSASignature
        BitcoinSignature2: LNECDSASignature
        Contents: UnsignedChannelAnnouncementMsg
    }

    interface IRoutingMsg

    interface ILightningSerializable<ChannelAnnouncementMsg> with
        member this.Deserialize ls =
            {
                NodeSignature1 = ls.ReadECDSACompact()
                NodeSignature2 = ls.ReadECDSACompact()
                BitcoinSignature1 = ls.ReadECDSACompact()
                BitcoinSignature2 = ls.ReadECDSACompact()

                Contents =
                    ILightningSerializable.deserialize<UnsignedChannelAnnouncementMsg>(
                        ls
                    )
            }

        member this.Serialize ls =
            ls.Write(this.NodeSignature1)
            ls.Write(this.NodeSignature2)
            ls.Write(this.BitcoinSignature1)
            ls.Write(this.BitcoinSignature2)

            (this.Contents
            :> ILightningSerializable<UnsignedChannelAnnouncementMsg>)
                .Serialize(ls)

/// `channel_update` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
/// without signatures
[<CLIMutable>]
type UnsignedChannelUpdateMsg =
    {
        ChainHash: uint256
        ShortChannelId: ShortChannelId
        Timestamp: uint32
        MessageFlags: uint8
        ChannelFlags: uint8
        CLTVExpiryDelta: BlockHeightOffset16
        HTLCMinimumMSat: LNMoney
        FeeBaseMSat: LNMoney
        FeeProportionalMillionths: uint32
        HTLCMaximumMSat: OptionalField<LNMoney>
    }

    interface IRoutingMsg

    interface ILightningSerializable<UnsignedChannelUpdateMsg> with
        member this.Deserialize
            (ls: LightningReaderStream)
            : UnsignedChannelUpdateMsg =
            let chainHash = ls.ReadUInt256(true)

            let shortChannelId =
                ls.ReadUInt64(false) |> ShortChannelId.FromUInt64

            let timestamp = ls.ReadUInt32(false)
            let messageFlags = ls.ReadByte()
            let channelFlags = ls.ReadByte()
            let cltvExpiryDelta = ls.ReadUInt16(false) |> BlockHeightOffset16

            let htlcMinimumMSat = ls.ReadUInt64(false) |> LNMoney.MilliSatoshis

            let feeBaseMSat =
                ls.ReadUInt32(false) |> uint64 |> LNMoney.MilliSatoshis

            let feeProportionalMillionths = ls.ReadUInt32(false)

            let htlcMaximumMSat =
                if ((messageFlags &&& 0b00000001uy) = 1uy) then
                    ls.ReadUInt64(false) |> LNMoney.MilliSatoshis |> Some
                else
                    None

            {
                ChainHash = chainHash
                ShortChannelId = shortChannelId
                Timestamp = timestamp
                MessageFlags = messageFlags
                ChannelFlags = channelFlags
                CLTVExpiryDelta = cltvExpiryDelta
                HTLCMinimumMSat = htlcMinimumMSat
                FeeBaseMSat = feeBaseMSat
                FeeProportionalMillionths = feeProportionalMillionths
                HTLCMaximumMSat = htlcMaximumMSat
            }

        member this.Serialize(ls: LightningWriterStream) : unit =
            ls.Write(this.ChainHash, true)
            ls.Write(this.ShortChannelId)
            ls.Write(this.Timestamp, false)
            ls.Write(this.MessageFlags)
            ls.Write(this.ChannelFlags)
            ls.Write(this.CLTVExpiryDelta.Value, false)
            ls.Write(this.HTLCMinimumMSat.MilliSatoshi, false)
            ls.Write(uint32 this.FeeBaseMSat.MilliSatoshi, false)
            ls.Write(uint32 this.FeeProportionalMillionths, false)

            match this.HTLCMaximumMSat with
            | Some s -> ls.Write(s.MilliSatoshi, false)
            | None -> ()


/// `channel_update` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type ChannelUpdateMsg =
    {
        Signature: LNECDSASignature
        Contents: UnsignedChannelUpdateMsg
    }

    member this.IsNode1 = (this.Contents.ChannelFlags &&& 1uy) = 0uy
    interface IRoutingMsg

    interface ILightningSerializable<ChannelUpdateMsg> with
        member this.Deserialize ls =
            {
                Signature = ls.ReadECDSACompact()
                Contents =
                    ILightningSerializable.deserialize<UnsignedChannelUpdateMsg>(
                        ls
                    )
            }

        member this.Serialize ls =
            ls.Write(this.Signature)

            (this.Contents :> ILightningSerializable<UnsignedChannelUpdateMsg>)
                .Serialize(ls)

/// inner data for failure msg described in [bolt04](https://github.com/lightning/bolts/blob/master/04-onion-routing.md#failure-messages)
type FailureMsgData =
    | InvalidRealm
    | TemporaryNodeFailure
    | PermanentNodeFailure
    | RequiredNodeFeatureMissing
    | InvalidOnionVersion of onionHash: uint256
    | InvalidOnionHmac of onionHash: uint256
    | InvalidOnionKey of onionHash: uint256
    | TemporaryChannelFailure of update: ChannelUpdateMsg
    | PermanentChannelFailure
    | RequiredChannelFeatureMissing
    | UnknownNextPeer
    | AmountBelowMinimum of amount: LNMoney * update: ChannelUpdateMsg
    | FeeInsufficient of amount: LNMoney * update: ChannelUpdateMsg
    | ChannelDisabled of Flags: uint16 * update: ChannelUpdateMsg
    | IncorrectCLTVExpiry of expiry: BlockHeight * update: ChannelUpdateMsg
    | UnknownPaymentHash
    | IncorrectPaymentAmount
    | ExpiryTooSoon of update: ChannelUpdateMsg
    | FinalExpiryTooSoon
    | FinalIncorrectCLTVExpiry of expiry: BlockHeight
    | FinalIncorrectCLTVAmount of amountMSat: LNMoney
    | ExpiryTooFar
    | Unknown of array<byte>

/// `failuremsg` in [bolt04](https://github.com/lightning/bolts/blob/master/04-onion-routing.md#failure-messages)
[<CLIMutable>]
type FailureMsg =
    {
        Data: FailureMsgData
        Code: FailureCode
    }

    interface ILightningSerializable<FailureMsg> with
        member this.Deserialize(r: LightningReaderStream) : FailureMsg =
            let t = r.ReadUInt16(false)

            {
                Code = t |> FailureCode
                Data =
                    match t with
                    | (INVALID_REALM) -> InvalidRealm
                    | (TEMPORARY_NODE_FAILURE) -> TemporaryNodeFailure
                    | (PERMANENT_NODE_FAILURE) -> PermanentNodeFailure
                    | (REQUIRED_NODE_FEATURE_MISSING) ->
                        RequiredNodeFeatureMissing
                    | (INVALID_ONION_VERSION) ->
                        let v = r.ReadUInt256(true)
                        InvalidOnionVersion(v)
                    | (INVALID_ONION_HMAC) ->
                        r.ReadUInt256(true) |> InvalidOnionHmac
                    | (INVALID_ONION_KEY) ->
                        r.ReadUInt256(true) |> InvalidOnionKey
                    | (TEMPORARY_CHANNEL_FAILURE) ->
                        let d =
                            ILightningSerializable.deserialize<ChannelUpdateMsg>(
                                r
                            )

                        d |> TemporaryChannelFailure
                    | (PERMANENT_CHANNEL_FAILURE) -> PermanentChannelFailure
                    | (REQUIRED_CHANNEL_FEATURE_MISSING) ->
                        RequiredChannelFeatureMissing
                    | (UNKNOWN_NEXT_PEER) -> UnknownNextPeer
                    | (AMOUNT_BELOW_MINIMUM) ->
                        let amountMSat =
                            r.ReadUInt64(false) |> LNMoney.MilliSatoshis

                        let d: ChannelUpdateMsg =
                            ILightningSerializable.deserialize r

                        (amountMSat, d) |> AmountBelowMinimum
                    | (FEE_INSUFFICIENT) ->
                        let amountMSat =
                            r.ReadUInt64(false) |> LNMoney.MilliSatoshis

                        let d: ChannelUpdateMsg =
                            ILightningSerializable.deserialize r

                        (amountMSat, d) |> FeeInsufficient
                    | (CHANNEL_DISABLED) ->
                        let flags = r.ReadUInt16(false)

                        let d: ChannelUpdateMsg =
                            ILightningSerializable.deserialize r

                        (flags, d) |> ChannelDisabled
                    | (INOCCORRECT_CLTV_EXPIRY) ->
                        let expiry = r.ReadUInt32(false) |> BlockHeight

                        let d: ChannelUpdateMsg =
                            ILightningSerializable.deserialize r

                        (expiry, d) |> IncorrectCLTVExpiry
                    | (UNKNOWN_PAYMENT_HASH) -> UnknownPaymentHash
                    | (INCORRECT_PAYMENT_AMOUNT) -> IncorrectPaymentAmount
                    | (EXPIRY_TOO_SOON) ->
                        let d: ChannelUpdateMsg =
                            ILightningSerializable.deserialize r

                        d |> ExpiryTooSoon
                    | FINAL_EXPIRY_TOO_SOON -> FinalExpiryTooSoon
                    | (FINAL_INCORRECT_CLTV_EXPIRY) ->
                        let expiry = r.ReadUInt32(false) |> BlockHeight
                        expiry |> FinalIncorrectCLTVExpiry
                    | (FINAL_INCORRECT_HTLC_AMOUNT) ->
                        let expiry =
                            r.ReadUInt64(false) |> LNMoney.MilliSatoshis

                        expiry |> FinalIncorrectCLTVAmount
                    | (EXPIRY_TOO_FAR) -> ExpiryTooFar
                    | _ -> r.ReadAll() |> Unknown
            }

        member this.Serialize(w: LightningWriterStream) : unit =
            w.Write(this.Code.Value, false)

            match this.Data with
            | InvalidOnionVersion onionHash -> w.Write(onionHash, false)
            | InvalidOnionHmac onionHash -> w.Write(onionHash, false)
            | InvalidOnionKey onionHash -> w.Write(onionHash, false)
            | TemporaryChannelFailure update ->
                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | AmountBelowMinimum(amount, update) ->
                w.Write(uint64 amount.Value, false)

                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | FeeInsufficient(amount, update) ->
                w.Write(uint64 amount.Value, false)

                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | ChannelDisabled(flags, update) ->
                w.Write(flags, false)

                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | IncorrectCLTVExpiry(expiry, update) ->
                w.Write(expiry.Value, false)

                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | ExpiryTooSoon update ->
                (update :> ILightningSerializable<ChannelUpdateMsg>)
                    .SerializeWithLen(w)
            | FinalIncorrectCLTVExpiry expiry -> w.Write(expiry.Value, false)
            | FinalIncorrectCLTVAmount amountMSat ->
                w.Write(amountMSat.Value, false)
            | FailureMsgData.Unknown b -> w.Write(b)
            | _ -> ()


[<CLIMutable>]
type ErrorMsg =
    {
        ChannelId: WhichChannel
        Data: array<byte>
    }

    interface ISetupMsg

    interface ILightningSerializable<ErrorMsg> with
        member this.Deserialize ls =
            {
                ChannelId =
                    match ls.ReadUInt256(true) with
                    | id when id = uint256.Zero -> All
                    | id -> SpecificChannel(ChannelId id)

                Data = ls.ReadWithLen()
            }

        member this.Serialize ls =
            match this.ChannelId with
            | SpecificChannel(ChannelId id) -> ls.Write(id.ToBytes())
            | All -> ls.Write(Array.zeroCreate 32)

            ls.WriteWithLen(this.Data)

    member this.GetFailureMsgData() =
        let minPrintableAsciiChar = 32uy

        let isPrintableAsciiChar(asciiChar: byte) =
            asciiChar >= minPrintableAsciiChar

        let isPrintableAsciiString =
            not
            <| Seq.exists
                (fun asciiChar -> not(isPrintableAsciiChar asciiChar))
                this.Data

        if isPrintableAsciiString then
            System.Text.ASCIIEncoding.ASCII.GetString this.Data
        else
            Seq.fold
                (fun msg (asciiChar: byte) -> sprintf "%s %02x" msg asciiChar)
                "<error contains non-printable binary data>:"
                this.Data

and WhichChannel =
    | SpecificChannel of ChannelId
    | All


[<RequireQualifiedAccess>]
[<CLIMutable>]
type WarningMsg =
    {
        ChannelId: WhichChannel
        Data: array<byte>
    }

    interface ISetupMsg

    interface ILightningSerializable<WarningMsg> with
        member this.Deserialize readStream =
            {
                ChannelId =
                    match readStream.ReadUInt256 true with
                    | id when id = uint256.Zero -> All
                    | id -> SpecificChannel(ChannelId id)

                Data = readStream.ReadWithLen()
            }

        member this.Serialize writeStream =
            match this.ChannelId with
            | SpecificChannel(ChannelId id) -> writeStream.Write(id.ToBytes())
            | All -> writeStream.Write(Array.zeroCreate 32)

            writeStream.WriteWithLen this.Data

    member this.GetFailureMsgData() =
        let minPrintableAsciiChar = 32uy

        let isPrintableAsciiChar(asciiChar: byte) =
            asciiChar >= minPrintableAsciiChar

        let isPrintableAsciiString =
            this.Data |> Array.forall isPrintableAsciiChar

        if isPrintableAsciiString then
            System.Text.ASCIIEncoding.ASCII.GetString this.Data
        else
            Seq.fold
                (fun msg (asciiChar: byte) -> sprintf "%s %02x" msg asciiChar)
                "<warning contains non-printable binary data>:"
                this.Data


#nowarn "0044" // "This construct is deprecated" warning
// sadly we don't have a way to restore warnings yet.
// ref: https://github.com/fsharp/fslang-suggestions/issues/278

[<Obsolete>]
type ErrorAction =
    | DisconnectPeer of option<ErrorMsg>
    | IgnoreError
    | SendErrorMessage of ErrorMsg

[<Obsolete>]
type HandleError =
    {
        Error: string
        Action: option<ErrorAction>
    }


/// Struct used to return valeus from revoke_and_ack messages, cotaining a bunch of commitment
/// transaction updates if they were pending.
type CommitmentUpdate =
    {
        UpdateAddHTLCs: list<UpdateAddHTLCMsg>
        UpdateFulfillHTLCs: list<UpdateFulfillHTLCMsg>
        UpdateFailHTLCs: list<UpdateFailHTLCMsg>
        UpdateFailMalformedHTLCs: list<UpdateFailMalformedHTLCMsg>
        UpdateFee: option<UpdateFeeMsg>
        CommitmentSigned: CommitmentSignedMsg
    }

#nowarn "0044" // "This construct is deprecated" warning

[<Obsolete>]
type ChannelClosed =
    {
        ShortChannelId: ShortChannelId
        /// when this true, this channel should be permanently removed from the
        /// consideration. Otherwise, this channel can be restored as new ChannelUpdateMsg is received
        IsPermanent: bool
    }

/// The information we received from a peer along the route of a payment we originated. This is
/// returned by ChannelMessageHandler.HandleUpdateFailHTLC to be passed into
/// RoutingMessageHandler.HandleHTLCFailChannelUpdate to update our network map.
[<Obsolete>]
type HTLCFailChannelUpdate =
    {
        ChannelUpdateMessage: ChannelUpdateMsg
        ChannelClosed: ChannelClosed
        NodeFailure: NodeFailure
    }


and NodeFailure =
    {
        NodeId: NodeId
        IsPermanent: bool
    }


/// `query_short_channel_ids` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type QueryShortChannelIdsMsg =
    {
        ChainHash: uint256
        ShortIdsEncodingType: EncodingType
        ShortIds: array<ShortChannelId>
        TLVs: array<QueryShortChannelIdsTLV>
    }

    interface IQueryMsg

    interface ILightningSerializable<QueryShortChannelIdsMsg> with
        member this.Deserialize(ls: LightningReaderStream) =
            let chainHash = ls.ReadUInt256(true)
            let shortIdsWithFlag = ls.ReadWithLen()

            let shortIdsEncodingType =
                LanguagePrimitives.EnumOfValue<byte, EncodingType>(
                    shortIdsWithFlag.[0]
                )

            let shortIds =
                Decoder.decodeShortChannelIds
                    shortIdsEncodingType
                    (shortIdsWithFlag.[1..])

            let tlvs =
                ls.ReadTLVStream()
                |> Array.map(QueryShortChannelIdsTLV.FromGenericTLV)

            let queryFlags =
                tlvs
                |> Seq.choose(
                    function
                    | QueryShortChannelIdsTLV.QueryFlags(_, y) -> Some(y)
                    | _ -> None
                )
                |> Seq.tryExactlyOne

            match queryFlags with
            | None -> ()
            | Some flags ->
                if (shortIds.Length <> (flags |> Seq.length)) then
                    raise
                    <| FormatException(
                        sprintf
                            "query_short_channel_ids have different length for short_ids(%A) and query_flags! (%A)"
                            shortIds
                            flags
                    )

            {
                ChainHash = chainHash
                ShortIdsEncodingType = shortIdsEncodingType
                ShortIds = shortIds
                TLVs = tlvs
            }

        member this.Serialize ls =
            ls.Write(this.ChainHash, true)

            let encodedIds =
                this.ShortIds
                |> Encoder.encodeShortChannelIds(this.ShortIdsEncodingType)

            [
                [| (byte) this.ShortIdsEncodingType |]
                encodedIds
            ]
            |> Array.concat
            |> ls.WriteWithLen

            this.TLVs
            |> Array.map(fun tlv -> tlv.ToGenericTLV())
            |> ls.WriteTLVStream

/// `reply_short_channel_ids_end` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type ReplyShortChannelIdsEndMsg =
    {
        ChainHash: uint256
        Complete: bool
    }

    interface IQueryMsg

    interface ILightningSerializable<ReplyShortChannelIdsEndMsg> with
        member this.Deserialize ls =
            {
                ChainHash = ls.ReadUInt256(true)

                Complete =
                    let b = ls.ReadByte()

                    if (b = 0uy) then
                        false
                    else if (b = 1uy) then
                        true
                    else
                        raise
                        <| FormatException(
                            sprintf
                                "reply_short_channel_ids has unknown byte in `complete` field %A"
                                b
                        )
            }

        member this.Serialize ls =
            ls.Write(this.ChainHash, true)

            ls.Write(
                if this.Complete then
                    1uy
                else
                    0uy
            )

/// `query_channel_range` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type QueryChannelRangeMsg =
    {
        ChainHash: uint256
        FirstBlockNum: BlockHeight
        NumberOfBlocks: uint32
        TLVs: array<QueryChannelRangeTLV>
    }

    interface IQueryMsg

    interface ILightningSerializable<QueryChannelRangeMsg> with
        member this.Deserialize ls =
            {
                ChainHash = ls.ReadUInt256(true)
                FirstBlockNum = ls.ReadUInt32(false) |> BlockHeight
                NumberOfBlocks = ls.ReadUInt32(false)

                TLVs =
                    let r = ls.ReadTLVStream()
                    r |> Array.map(QueryChannelRangeTLV.FromGenericTLV)
            }

        member this.Serialize ls =
            ls.Write(this.ChainHash, true)
            ls.Write(this.FirstBlockNum.Value, false)
            ls.Write(this.NumberOfBlocks, false)

            this.TLVs
            |> Array.map(fun tlv -> tlv.ToGenericTLV())
            |> ls.WriteTLVStream

/// `reply_channel_range` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type ReplyChannelRangeMsg =
    {
        ChainHash: uint256
        FirstBlockNum: BlockHeight
        NumOfBlocks: uint32
        Complete: bool
        ShortIdsEncodingType: EncodingType
        ShortIds: array<ShortChannelId>
        TLVs: array<ReplyChannelRangeTLV>
    }

    interface IQueryMsg

    interface ILightningSerializable<ReplyChannelRangeMsg> with
        member this.Deserialize ls =
            let chainHash = ls.ReadUInt256(true)
            let firstBlockNum = ls.ReadUInt32(false) |> BlockHeight
            let numOfBlocks = ls.ReadUInt32(false)

            let complete =
                let b = ls.ReadByte()

                if b = 0uy then
                    false
                else if b = 1uy then
                    true
                else
                    raise
                    <| FormatException(
                        sprintf
                            "reply_channel_range has unknown byte in `complete` field %A"
                            b
                    )

            let shortIdsWithFlag = ls.ReadWithLen()

            let shortIdsEncodingType =
                LanguagePrimitives.EnumOfValue<byte, EncodingType>(
                    shortIdsWithFlag.[0]
                )

            let shortIds =
                Decoder.decodeShortChannelIds
                    shortIdsEncodingType
                    (shortIdsWithFlag.[1..])

            let tLVs =
                ls.ReadTLVStream()
                |> Array.map(ReplyChannelRangeTLV.FromGenericTLV)

            {
                ChainHash = chainHash
                FirstBlockNum = firstBlockNum
                NumOfBlocks = numOfBlocks
                Complete = complete
                ShortIdsEncodingType = shortIdsEncodingType
                ShortIds = shortIds
                TLVs = tLVs
            }

        member this.Serialize ls =
            ls.Write(this.ChainHash, true)
            ls.Write(this.FirstBlockNum.Value, false)
            ls.Write(this.NumOfBlocks, false)

            ls.Write(
                if this.Complete then
                    1uy
                else
                    0uy
            )

            let encodedIds =
                this.ShortIds
                |> Encoder.encodeShortChannelIds(this.ShortIdsEncodingType)

            [
                [| (byte) this.ShortIdsEncodingType |]
                encodedIds
            ]
            |> Array.concat
            |> ls.WriteWithLen

            this.TLVs
            |> Array.map(fun x -> x.ToGenericTLV())
            |> ls.WriteTLVStream

/// `gossip_timestamp_filter` in [bolt07](https://github.com/lightning/bolts/blob/master/07-routing-gossip.md)
[<CLIMutable>]
type GossipTimestampFilterMsg =
    {
        ChainHash: uint256
        FirstTimestamp: uint32
        TimestampRange: uint32
    }

    interface IQueryMsg

    interface ILightningSerializable<GossipTimestampFilterMsg> with
        member this.Deserialize ls =
            {
                ChainHash = ls.ReadUInt256(true)
                FirstTimestamp = ls.ReadUInt32(false)
                TimestampRange = ls.ReadUInt32(false)
            }

        member this.Serialize ls =
            ls.Write(this.ChainHash, true)
            ls.Write(this.FirstTimestamp, false)
            ls.Write(this.TimestampRange, false)
