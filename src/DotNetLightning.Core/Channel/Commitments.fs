namespace DotNetLightning.Channel

open NBitcoin
open DotNetLightning.Utils
open DotNetLightning.Utils.Aether
open DotNetLightning.Utils.Aether.Operators
open DotNetLightning.Crypto
open DotNetLightning.Transactions
open DotNetLightning.Serialization.Msgs

open ResultUtils
open ResultUtils.Portability
open DotNetLightning.Transactions

type LocalChanges = {
    Proposed: IUpdateMsg list
    Signed: IUpdateMsg list
    ACKed: IUpdateMsg list
}
    with
        static member Zero = { Proposed = []; Signed = []; ACKed = [] }

        // -- lenses
        static member Proposed_: Lens<_, _> =
            (fun lc -> lc.Proposed),
            (fun ps lc -> { lc with Proposed = ps })
        static member Signed_: Lens<_, _> =
            (fun lc -> lc.Signed),
            (fun v lc -> { lc with Signed = v })

        static member ACKed_: Lens<_, _> =
            (fun lc -> lc.ACKed),
            (fun v lc -> { lc with ACKed = v })

        member this.All() =
            this.Proposed @ this.Signed @ this.ACKed

type RemoteChanges = { 
    Proposed: IUpdateMsg list
    Signed: IUpdateMsg list
    ACKed: IUpdateMsg list
}
    with
        static member Zero = { Proposed = []; Signed = []; ACKed = [] }
        static member Proposed_: Lens<_, _> =
            (fun lc -> lc.Proposed),
            (fun ps lc -> { lc with Proposed = ps })
        static member Signed_: Lens<_, _> =
            (fun lc -> lc.Signed),
            (fun v lc -> { lc with Signed = v })

        static member ACKed_: Lens<_, _> =
            (fun lc -> lc.ACKed),
            (fun v lc -> { lc with ACKed = v })


type PublishableTxs = {
    CommitTx: FinalizedTx
    HTLCTxs: FinalizedTx list
}

type LocalCommit = {
    Index: CommitmentNumber
    Spec: CommitmentSpec
    PublishableTxs: PublishableTxs
    /// These are not redeemable on-chain until we get a corresponding preimage.
    PendingHTLCSuccessTxs: HTLCSuccessTx list
}
type RemoteCommit = {
    Index: CommitmentNumber
    Spec: CommitmentSpec
    TxId: TxId
    RemotePerCommitmentPoint: PerCommitmentPoint
}

type RemoteNextCommitInfo =
    | Waiting of RemoteCommit
    | Revoked of PerCommitmentPoint
    with
        static member Waiting_: Prism<RemoteNextCommitInfo, RemoteCommit> =
            (fun remoteNextCommitInfo ->
                match remoteNextCommitInfo with
                | Waiting remoteCommit -> Some remoteCommit
                | Revoked _ -> None),
            (fun waitingForRevocation remoteNextCommitInfo ->
                match remoteNextCommitInfo with
                | Waiting _ -> Waiting waitingForRevocation
                | Revoked _ -> remoteNextCommitInfo)

        static member Revoked_: Prism<RemoteNextCommitInfo, PerCommitmentPoint> =
            (fun remoteNextCommitInfo ->
                match remoteNextCommitInfo with
                | Waiting _ -> None
                | Revoked commitmentPubKey -> Some commitmentPubKey),
            (fun commitmentPubKey remoteNextCommitInfo ->
                match remoteNextCommitInfo with
                | Waiting _ -> remoteNextCommitInfo
                | Revoked _ -> Revoked commitmentPubKey)

        member self.PerCommitmentPoint(): PerCommitmentPoint =
            match self with
            | Waiting remoteCommit -> remoteCommit.RemotePerCommitmentPoint
            | Revoked perCommitmentPoint -> perCommitmentPoint

type Amounts = 
    {
        ToLocal: Money
        ToRemote: Money
    }

type Commitments = {
    LocalCommit: LocalCommit
    RemoteCommit: RemoteCommit
    LocalChanges: LocalChanges
    RemoteChanges: RemoteChanges
    LocalNextHTLCId: HTLCId
    RemoteNextHTLCId: HTLCId
    OriginChannels: Map<HTLCId, HTLCSource>
    RemotePerCommitmentSecrets: PerCommitmentSecretStore
}
    with
        static member LocalChanges_: Lens<_, _> =
            (fun c -> c.LocalChanges),
            (fun v c -> { c with LocalChanges = v })
        static member RemoteChanges_: Lens<_, _> =
            (fun c -> c.RemoteChanges),
            (fun v c -> { c with RemoteChanges = v })

        member this.AddLocalProposal(proposal: IUpdateMsg) =
            let lens = Commitments.LocalChanges_ >-> LocalChanges.Proposed_
            Optic.map lens (fun proposalList -> proposal :: proposalList) this

        member this.AddRemoteProposal(proposal: IUpdateMsg) =
            let lens = Commitments.RemoteChanges_ >-> RemoteChanges.Proposed_
            Optic.map lens (fun proposalList -> proposal :: proposalList) this

        member this.IncrLocalHTLCId() = { this with LocalNextHTLCId = this.LocalNextHTLCId + 1UL }
        member this.IncrRemoteHTLCId() = { this with RemoteNextHTLCId = this.RemoteNextHTLCId + 1UL }

        member this.LocalHasChanges() =
            (not this.RemoteChanges.ACKed.IsEmpty) || (not this.LocalChanges.Proposed.IsEmpty)

        member this.RemoteHasChanges() =
            (not this.LocalChanges.ACKed.IsEmpty) || (not this.RemoteChanges.Proposed.IsEmpty)

        member internal this.LocalHasUnsignedOutgoingHTLCs() =
            this.LocalChanges.Proposed |> List.exists(fun p -> match p with | :? UpdateAddHTLCMsg -> true | _ -> false)

        member internal this.RemoteHasUnsignedOutgoingHTLCs() =
            this.RemoteChanges.Proposed |> List.exists(fun p -> match p with | :? UpdateAddHTLCMsg -> true | _ -> false)

        member internal this.HasNoPendingHTLCs (remoteNextCommitInfo: RemoteNextCommitInfo) =
            this.LocalCommit.Spec.HTLCs.IsEmpty
            && this.RemoteCommit.Spec.HTLCs.IsEmpty
            && (remoteNextCommitInfo |> function Waiting _ -> false | Revoked _ -> true)

        member internal this.GetHTLCCrossSigned (remoteNextCommitInfo: RemoteNextCommitInfo)
                                                (directionRelativeToLocal: Direction)
                                                (htlcId: HTLCId)
                                                    : Option<UpdateAddHTLCMsg> =
            let remoteSigned =
                this.LocalCommit.Spec.HTLCs
                |> Map.tryPick (fun _k v ->
                    if v.Direction = directionRelativeToLocal && v.Add.HTLCId = htlcId then
                        Some v
                    else None
                )

            let localSigned =
                let remoteCommit =
                    match remoteNextCommitInfo with
                    | Revoked _ -> this.RemoteCommit
                    | Waiting nextRemoteCommit -> nextRemoteCommit
                remoteCommit.Spec.HTLCs
                |> Map.tryPick(fun _k v ->
                    if v.Direction = directionRelativeToLocal.Opposite && v.Add.HTLCId = htlcId then
                        Some v
                    else
                        None
                )

            match remoteSigned, localSigned with
            | Some _, Some htlcIn -> htlcIn.Add |> Some
            | _ -> None

        static member RemoteCommitAmount (isLocalFunder: bool)
                                         (remoteParams: RemoteParams)
                                         (remoteCommit: RemoteCommit)
                                             : Amounts =
            let commitFee = Transactions.commitTxFee
                                remoteParams.DustLimitSatoshis
                                remoteCommit.Spec
            
            let (toLocalAmount, toRemoteAmount) =
                if isLocalFunder then
                    (remoteCommit.Spec.ToLocal.Satoshi
                     |> Money.Satoshis),
                    (remoteCommit.Spec.ToRemote.Satoshi
                     |> Money.Satoshis) - commitFee
                else
                    (remoteCommit.Spec.ToLocal.Satoshi
                     |> Money.Satoshis) - commitFee,
                    (remoteCommit.Spec.ToRemote.Satoshi
                     |> Money.Satoshis)

            {Amounts.ToLocal = toLocalAmount; ToRemote = toRemoteAmount}

        static member LocalCommitAmount (isLocalFunder: bool)
                                        (localParams: LocalParams)
                                        (localCommit: LocalCommit)
                                            : Amounts =
            let commitFee = Transactions.commitTxFee
                                localParams.DustLimitSatoshis
                                localCommit.Spec
            
            let (toLocalAmount, toRemoteAmount) =
                if isLocalFunder then
                    (localCommit.Spec.ToLocal.Satoshi
                     |> Money.Satoshis) - commitFee,
                    (localCommit.Spec.ToRemote.Satoshi
                     |> Money.Satoshis)
                else
                    (localCommit.Spec.ToLocal.Satoshi
                     |> Money.Satoshis),
                    (localCommit.Spec.ToRemote.Satoshi
                     |> Money.Satoshis) - commitFee

            {Amounts.ToLocal = toLocalAmount; ToRemote = toRemoteAmount}
