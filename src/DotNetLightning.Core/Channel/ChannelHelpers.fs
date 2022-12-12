namespace DotNetLightning.Channel

open System

open DotNetLightning.Chain
open DotNetLightning.Utils
open DotNetLightning.Channel
open DotNetLightning.Crypto
open DotNetLightning.Serialization.Msgs
open DotNetLightning.Transactions

open ResultUtils
open ResultUtils.Portability

open NBitcoin

/// cousin of `ChannelHelpers` module which only includes very primitive function.
module internal ChannelConstantHelpers =
    let deriveOurDustLimitSatoshis(feeEstimator: IFeeEstimator) : Money =
        let (FeeRatePerKw atOpenBackGroundFee) =
            feeEstimator.GetEstSatPer1000Weight(ConfirmationTarget.Background)

        (Money.Satoshis(
            (uint64 atOpenBackGroundFee) * B_OUTPUT_PLUS_SPENDING_INPUT_WEIGHT
            / 1000UL
         ),
         Money.Satoshis(546UL))
        |> Money.Max

    let getOurChannelReserve(channelValue: Money) =
        let q = channelValue / 100L
        Money.Min(channelValue, Money.Max(q, Money.Satoshis(1L)))


module ChannelSyncing =
    type SyncResult =
        | RemoteLate
        | LocalLateProven of
            ourLocalCommitmentNumber: CommitmentNumber *
            theirRemoteCommitmentNumber: CommitmentNumber *
            currentPerCommitmentPoint: PerCommitmentPoint
        | LocalLateUnproven of
            ourRemoteCommitmentNumber: CommitmentNumber *
            theirLocalCommitmentNumber: CommitmentNumber
        | RemoteLying of
            ourLocalCommitmentNumber: CommitmentNumber *
            theirRemoteCommitmentNumber: CommitmentNumber *
            invalidPerCommitmentSecret: option<PerCommitmentPoint>
        | Success of retransmitRevocation: list<ILightningMsg>

    let checkSync
        (channelPrivKeys: ChannelPrivKeys)
        (savedChannelState: SavedChannelState)
        (remoteNextCommitInfo: Option<RemoteNextCommitInfo>)
        (remoteChannelReestablish: ChannelReestablishMsg)
        : SyncResult =
        // NOTE: since CommitmentNumber in DNL goes backwards (from 2^48 to 0), all comparison signs are reversed
        let checkRemoteCommit(retransmitRevocationList: list<ILightningMsg>) =
            match remoteNextCommitInfo with
            | Some(Waiting waitingForRevocation) when
                remoteChannelReestablish.NextCommitmentNumber = waitingForRevocation.NextRemoteCommit.Index
                ->
                // we just sent a new commit_sig but they didn't receive it
                // we resend the same updates and the same sig, and preserve the same ordering
                let signedUpdates =
                    savedChannelState.LocalChanges.Signed
                    |> List.map(fun msg -> msg :> ILightningMsg)

                let commitSigList =
                    waitingForRevocation.SentSig :> ILightningMsg
                    |> List.singleton

                match List.tryHead retransmitRevocationList with
                | None -> SyncResult.Success(signedUpdates @ commitSigList)
                | Some _ when
                    savedChannelState.LocalCommit.Index < waitingForRevocation.SentAfterLocalCommitIndex
                    ->
                    SyncResult.Success(
                        signedUpdates @ commitSigList @ retransmitRevocationList
                    )
                | Some _ ->
                    SyncResult.Success(
                        retransmitRevocationList @ signedUpdates @ commitSigList
                    )
            | Some(Waiting waitingForRevocation) when
                remoteChannelReestablish.NextCommitmentNumber = (waitingForRevocation.NextRemoteCommit.Index.NextCommitment
                                                                     ())
                ->
                // we just sent a new commit_sig, they have received it but we haven't received their revocation
                SyncResult.Success retransmitRevocationList
            | Some(Waiting waitingForRevocation) when
                remoteChannelReestablish.NextCommitmentNumber > waitingForRevocation.NextRemoteCommit.Index
                ->
                SyncResult.RemoteLate
            | Some(Waiting waitingForRevocation) ->
                SyncResult.LocalLateUnproven(
                    waitingForRevocation.NextRemoteCommit.Index,
                    remoteChannelReestablish.NextCommitmentNumber.PreviousCommitment
                        ()
                )
            | Some(Revoked _) when
                remoteChannelReestablish.NextCommitmentNumber = savedChannelState.RemoteCommit.Index.NextCommitment
                                                                    ()
                ->
                SyncResult.Success retransmitRevocationList
            | Some(Revoked _) when
                remoteChannelReestablish.NextCommitmentNumber > savedChannelState.RemoteCommit.Index.NextCommitment
                                                                    ()
                ->
                SyncResult.RemoteLate
            | Some(Revoked _) ->
                SyncResult.LocalLateUnproven(
                    savedChannelState.RemoteCommit.Index,
                    remoteChannelReestablish.NextCommitmentNumber.PreviousCommitment
                        ()
                )
            | None ->
                //I think this means the funding isn't locked yet so who cares
                SyncResult.Success List.empty

        if savedChannelState.LocalCommit.Index = remoteChannelReestablish.NextRevocationNumber then
            checkRemoteCommit List.empty
        elif savedChannelState.LocalCommit.Index = remoteChannelReestablish.NextRevocationNumber.NextCommitment
                                                       () then
            // they just sent a new commit_sig, we have received it but they didn't receive our revocation
            let localPerCommitmentSecret =
                channelPrivKeys.CommitmentSeed.DerivePerCommitmentSecret
                    savedChannelState.LocalCommit.Index

            let localNextPerCommitmentPoint =
                let perCommitmentSecret =
                    channelPrivKeys.CommitmentSeed.DerivePerCommitmentSecret(
                        savedChannelState
                            .LocalCommit
                            .Index
                            .NextCommitment()
                            .NextCommitment()
                    )

                perCommitmentSecret.PerCommitmentPoint()

            let nextMsg =
                {
                    RevokeAndACKMsg.ChannelId =
                        savedChannelState.StaticChannelConfig.ChannelId()
                    PerCommitmentSecret = localPerCommitmentSecret
                    NextPerCommitmentPoint = localNextPerCommitmentPoint
                }
                :> ILightningMsg

            checkRemoteCommit(List.singleton nextMsg)
        elif savedChannelState.LocalCommit.Index < remoteChannelReestablish.NextRevocationNumber.NextCommitment
                                                       () then
            SyncResult.RemoteLate
        else
            match remoteChannelReestablish.DataLossProtect with
            | Some dataLossProtect ->
                if
                    Some
                        (
                            channelPrivKeys
                                .CommitmentSeed
                                .DerivePerCommitmentSecret(
                                    remoteChannelReestablish.NextRevocationNumber.PreviousCommitment
                                        ()
                                )
                        ) = dataLossProtect.YourLastPerCommitmentSecret
                then
                    SyncResult.LocalLateProven(
                        savedChannelState.LocalCommit.Index,
                        remoteChannelReestablish.NextRevocationNumber,
                        dataLossProtect.MyCurrentPerCommitmentPoint
                    )
                else
                    SyncResult.RemoteLying(
                        savedChannelState.LocalCommit.Index,
                        remoteChannelReestablish.NextRevocationNumber,
                        dataLossProtect.YourLastPerCommitmentSecret
                        |> Option.map(fun secret -> secret.PerCommitmentPoint())
                    )
            | None -> failwith "data_loss_protect is absent"


module ClosingHelpers =
    let TxVersionNumberOfCommitmentTxs = 2u

    type ValidateCommitmentTxError =
        | InvalidTxVersionForCommitmentTx of uint32
        | TxHasNoInputs
        | TxHasMultipleInputs of int
        | DoesNotSpendChannelFunds of OutPoint
        | InvalidLockTimeAndSequenceForCommitmentTx of LockTime * Sequence

        member this.Message: string =
            match this with
            | InvalidTxVersionForCommitmentTx version ->
                sprintf "invalid tx version for commitment tx (%i)" version
            | TxHasNoInputs -> "tx has no inputs"
            | TxHasMultipleInputs n -> sprintf "tx has multiple inputs (%i)" n
            | DoesNotSpendChannelFunds outPoint ->
                sprintf
                    "tx does not spend from the channel funds but spends from a different \
                    outpoint (%s)"
                    (outPoint.ToString())
            | InvalidLockTimeAndSequenceForCommitmentTx(lockTime, sequence) ->
                sprintf
                    "invalid lock time and sequence for commitment tx \
                    (locktime = %s, sequence = %s)"
                    (lockTime.ToString())
                    (sequence.ToString())

    type OutputClaimError =
        | BalanceBelowDustLimit
        | UnknownClosingTx
        | Inapplicable

    type ClosingResult =
        {
            MainOutput: Result<TransactionBuilder, OutputClaimError>
            AnchorOutput: Result<TransactionBuilder, OutputClaimError>
        }

    type HtlcTransaction =
        | Success of
            htlcId: HTLCId *
            spk: Script *
            preimage: PaymentPreimage *
            amount: LNMoney
        | Timeout of
            htlcId: HTLCId *
            spk: Script *
            blockHeight: uint32 *
            amount: LNMoney
        | Penalty of redeemScript: Script * amount: LNMoney

        member this.Amount =
            match this with
            | Success(_, _, _, amount)
            | Timeout(_, _, _, amount)
            | Penalty(_, amount) -> amount

    let tryGetObscuredCommitmentNumber
        (fundingOutPoint: OutPoint)
        (transaction: Transaction)
        : Result<ObscuredCommitmentNumber, ValidateCommitmentTxError> =
        result {
            if transaction.Version <> TxVersionNumberOfCommitmentTxs then
                return!
                    Error <| InvalidTxVersionForCommitmentTx transaction.Version

            if transaction.Inputs.Count = 0 then
                return! Error <| TxHasNoInputs

            if transaction.Inputs.Count > 1 then
                return! Error <| TxHasMultipleInputs transaction.Inputs.Count

            let txIn = Seq.exactlyOne transaction.Inputs

            if fundingOutPoint <> txIn.PrevOut then
                return! Error <| DoesNotSpendChannelFunds txIn.PrevOut

            match
                ObscuredCommitmentNumber.TryFromLockTimeAndSequence
                    transaction.LockTime
                    txIn.Sequence
                with
            | None ->
                return!
                    Error
                    <| InvalidLockTimeAndSequenceForCommitmentTx(
                        transaction.LockTime,
                        txIn.Sequence
                    )
            | Some obscuredCommitmentNumber -> return obscuredCommitmentNumber
        }

    let private ClaimAnchorOutput
        (commitTx: Transaction)
        (staticChannelConfig: StaticChannelConfig)
        (localChannelPrivKeys: ChannelPrivKeys)
        =
        result {
            let fundingPubKey =
                localChannelPrivKeys
                    .ToChannelPubKeys()
                    .FundingPubKey

            let anchorScriptPubKey = Scripts.anchor fundingPubKey

            let anchorIndexOpt =
                let anchorWitScriptPubKey =
                    anchorScriptPubKey.WitHash.ScriptPubKey

                Seq.tryFindIndex
                    (fun (txOut: TxOut) ->
                        txOut.ScriptPubKey = anchorWitScriptPubKey
                    )
                    commitTx.Outputs

            let! anchorIndex =
                match anchorIndexOpt with
                | Some anchorIndex -> Ok anchorIndex
                | None -> Error BalanceBelowDustLimit

            let transactionBuilder =
                Transactions.createDeterministicTransactionBuilder
                    staticChannelConfig.Network

            transactionBuilder.Extensions.Add(CommitmentAnchorExtension())

            return
                transactionBuilder
                    .AddKeys(localChannelPrivKeys.FundingPrivKey.RawKey())
                    .AddCoin(
                        ScriptCoin(
                            commitTx,
                            uint32 anchorIndex,
                            anchorScriptPubKey
                        )
                    )

        }

    let private findScriptPubKey (tx: Transaction) (spk: Script) =
        tx.Outputs.AsIndexedOutputs()
        |> Seq.find(fun output -> output.TxOut.ScriptPubKey = spk)

    module RemoteClose =
        let private ClaimMainOutput
            (commitTx: Transaction)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            (remotePerCommitmentPoint: PerCommitmentPoint)
            =
            result {
                let localChannelPubKeys =
                    localChannelPrivKeys.ToChannelPubKeys()

                let localPaymentPrivKey =
                    remotePerCommitmentPoint.DerivePaymentPrivKey
                        localChannelPrivKeys.PaymentBasepointSecret
                        staticChannelConfig.Type
                        true

                let localCommitmentPubKeys =
                    remotePerCommitmentPoint.DeriveCommitmentPubKeys
                        localChannelPubKeys
                        staticChannelConfig.Type
                        true

                let toRemoteScriptPubKey =
                    match staticChannelConfig.Type.CommitmentFormat with
                    | DefaultCommitmentFormat ->
                        localCommitmentPubKeys
                            .PaymentPubKey
                            .RawPubKey()
                            .WitHash
                            .ScriptPubKey
                    | AnchorCommitmentFormat ->
                        (Scripts.toRemoteDelayed
                            localCommitmentPubKeys.PaymentPubKey)
                            .WitHash
                            .ScriptPubKey


                let toRemoteIndexOpt =
                    Seq.tryFindIndex
                        (fun (txOut: TxOut) ->
                            txOut.ScriptPubKey = toRemoteScriptPubKey
                        )
                        commitTx.Outputs

                let! toRemoteIndex =
                    match toRemoteIndexOpt with
                    | Some toRemoteIndex -> Ok toRemoteIndex
                    | None -> Error <| BalanceBelowDustLimit

                let transactionBuilder =
                    (Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network)
                        .SetVersion(TxVersionNumberOfCommitmentTxs)
                        .AddKeys(localPaymentPrivKey.RawKey())

                return
                    match staticChannelConfig.Type.CommitmentFormat with
                    | DefaultCommitmentFormat ->
                        transactionBuilder.AddCoin(
                            Coin(commitTx, uint32 toRemoteIndex)
                        )
                    | AnchorCommitmentFormat ->
                        transactionBuilder.Extensions.Add(
                            CommitmentToDelayedRemoteExtension()
                        )

                        transactionBuilder.AddCoin(
                            ScriptCoin(
                                commitTx,
                                uint32 toRemoteIndex,
                                Scripts.toRemoteDelayed
                                    localCommitmentPubKeys.PaymentPubKey
                            ),
                            CoinOptions(Sequence = (Nullable <| Sequence 1u))
                        )
            }

        let UnresolvedHtlcList
            (closingTx: Transaction)
            (remoteCommit: RemoteCommit)
            (staticChannelConfig: StaticChannelConfig)
            (hash2preimage: PaymentHash -> option<PaymentPreimage>) //FIXME: should we check ProposedLocalChanges instead?
            =
            assert (closingTx.GetTxId() = remoteCommit.TxId)
            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let perCommitmentPoint = remoteCommit.RemotePerCommitmentPoint

            let localCommitmentPubKeys =
                let localChannelPubKeys =
                    staticChannelConfig.LocalChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    true

            let remoteCommitmentPubKeys =
                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    remoteChannelPubKeys
                    staticChannelConfig.Type
                    false

            let unresolvedOutgoingHtlcs =
                remoteCommit.Spec.OutgoingHTLCs
                |> Map.toList
                |> List.choose(fun (_id, htlcAddMsg) ->
                    match hash2preimage htlcAddMsg.PaymentHash with
                    | Some preimage ->
                        let redeem =
                            Scripts.htlcOffered
                                remoteCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.RevocationPubKey
                                htlcAddMsg.PaymentHash
                                commitmentFormat.HtlcCsvLock

                        let spk = redeem.WitHash.ScriptPubKey

                        let outputExistsInCommitmentTx =
                            closingTx.Outputs
                            |> Seq.exists(fun output ->
                                output.ScriptPubKey = spk
                            )

                        if outputExistsInCommitmentTx then
                            Some(
                                HtlcTransaction.Success(
                                    htlcAddMsg.HTLCId,
                                    spk,
                                    preimage,
                                    htlcAddMsg.Amount
                                )
                            )
                        else
                            None
                    | None -> None
                )

            let unresolvedIncomingHtlcs =
                remoteCommit.Spec.IncomingHTLCs
                |> Map.toList
                |> List.choose(fun (_id, htlcAddMsg) ->
                    let redeem =
                        Scripts.htlcReceived
                            remoteCommitmentPubKeys.HtlcPubKey
                            localCommitmentPubKeys.HtlcPubKey
                            localCommitmentPubKeys.RevocationPubKey
                            htlcAddMsg.PaymentHash
                            htlcAddMsg.CLTVExpiry.Value
                            commitmentFormat.HtlcCsvLock

                    let spk = redeem.WitHash.ScriptPubKey

                    let outputExistsInCommitmentTx =
                        closingTx.Outputs
                        |> Seq.exists(fun output -> output.ScriptPubKey = spk)

                    if outputExistsInCommitmentTx then
                        Some(
                            HtlcTransaction.Timeout(
                                htlcAddMsg.HTLCId,
                                spk,
                                htlcAddMsg.CLTVExpiry.Value,
                                htlcAddMsg.Amount
                            )
                        )
                    else
                        None
                )

            unresolvedIncomingHtlcs @ unresolvedOutgoingHtlcs

        let ClaimHtlcOutput
            (htlcInfo: HtlcTransaction)
            (closingTx: Transaction)
            (remoteCommit: RemoteCommit)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =
            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let remotePerCommitmentPoint = remoteCommit.RemotePerCommitmentPoint
            let localChannelPubKeys = localChannelPrivKeys.ToChannelPubKeys()

            let localCommitmentPubKeys =
                remotePerCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    true

            let remoteCommitmentPubKeys =
                remotePerCommitmentPoint.DeriveCommitmentPubKeys
                    staticChannelConfig.RemoteChannelPubKeys
                    staticChannelConfig.Type
                    false

            let htlcPrivKey =
                remotePerCommitmentPoint.DeriveHtlcPrivKey
                    localChannelPrivKeys.HtlcBasepointSecret

            match htlcInfo with
            | Timeout(htlcId, _, _, _) ->
                let htlcAddMsg =
                    remoteCommit.Spec.IncomingHTLCs |> Map.find htlcId

                let redeem =
                    Scripts.htlcReceived
                        remoteCommitmentPubKeys.HtlcPubKey
                        localCommitmentPubKeys.HtlcPubKey
                        localCommitmentPubKeys.RevocationPubKey
                        htlcAddMsg.PaymentHash
                        htlcAddMsg.CLTVExpiry.Value
                        commitmentFormat.HtlcCsvLock

                let spk = redeem.WitHash.ScriptPubKey

                let txIn = findScriptPubKey closingTx spk

                let txb =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let scriptCoin = ScriptCoin(txIn, redeem)
                // we have already done dust limit check above
                txb.DustPrevention <- false
                txb.Extensions.Add(HtlcReceivedExtension None)

                txb
                    .AddCoin(
                        scriptCoin,
                        CoinOptions(
                            Sequence =
                                (Nullable
                                 <| Sequence
                                     commitmentFormat.HtlcTxInputSequence)
                        )
                    )
                    .AddKeys(htlcPrivKey.RawKey())
                    .SetVersion(2u)
                    .SetLockTime(!>htlcAddMsg.CLTVExpiry.Value)
                |> ignore<TransactionBuilder>

                txb, false
            | Success(htlcId, _, preImage, _) ->
                let htlcAddMsg =
                    remoteCommit.Spec.OutgoingHTLCs |> Map.find htlcId

                let redeem =
                    Scripts.htlcOffered
                        remoteCommitmentPubKeys.HtlcPubKey
                        localCommitmentPubKeys.HtlcPubKey
                        localCommitmentPubKeys.RevocationPubKey
                        htlcAddMsg.PaymentHash
                        commitmentFormat.HtlcCsvLock

                let spk = redeem.WitHash.ScriptPubKey

                let txIn = findScriptPubKey closingTx spk

                let txb =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let scriptCoin = ScriptCoin(txIn, redeem)
                // we have already done dust limit check above
                txb.DustPrevention <- false
                txb.Extensions.Add(HtlcOfferedExtension(Some preImage))

                txb
                    .AddCoin(
                        scriptCoin,
                        CoinOptions(
                            Sequence =
                                (Nullable
                                 <| Sequence
                                     commitmentFormat.HtlcTxInputSequence)
                        )
                    )
                    .AddKeys(htlcPrivKey.RawKey())
                    .SetVersion(2u)
                |> ignore<TransactionBuilder>

                txb, false
            | Penalty _ ->
                failwith
                    "Should not happen because only RevokedClose.UnresolvedHtlcList uses `Penalty` case"

        let ClaimCommitTxOutputs
            (closingTx: Transaction)
            (staticChannelConfig: StaticChannelConfig)
            (channelPrivKeys: ChannelPrivKeys)
            (remoteCommit: RemoteCommit)
            (storedRemotePerCommitmentPoint: PerCommitmentPoint option)
            =
            assert (remoteCommit.TxId = closingTx.GetTxId())

            {
                MainOutput =
                    ClaimMainOutput
                        closingTx
                        staticChannelConfig
                        channelPrivKeys
                        (match storedRemotePerCommitmentPoint with
                         | Some point -> point
                         | None -> remoteCommit.RemotePerCommitmentPoint)
                AnchorOutput =
                    ClaimAnchorOutput
                        closingTx
                        staticChannelConfig
                        channelPrivKeys
            }

    module LocalClose =
        let private ClaimMainOutput
            (commitTx: Transaction)
            (commitmentNumber: CommitmentNumber)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =
            result {
                let localChannelPubKeys =
                    localChannelPrivKeys.ToChannelPubKeys()

                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                let perCommitmentPoint =
                    localChannelPrivKeys.CommitmentSeed.DerivePerCommitmentPoint
                        commitmentNumber

                let localCommitmentPubKeys =
                    perCommitmentPoint.DeriveCommitmentPubKeys
                        localChannelPubKeys
                        staticChannelConfig.Type
                        false

                let remoteCommitmentPubKeys =
                    perCommitmentPoint.DeriveCommitmentPubKeys
                        remoteChannelPubKeys
                        staticChannelConfig.Type
                        true

                let transactionBuilder =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let toLocalScriptPubKey =
                    Scripts.toLocalDelayed
                        remoteCommitmentPubKeys.RevocationPubKey
                        staticChannelConfig.RemoteParams.ToSelfDelay
                        localCommitmentPubKeys.DelayedPaymentPubKey

                let toLocalIndexOpt =
                    let toLocalWitScriptPubKey =
                        toLocalScriptPubKey.WitHash.ScriptPubKey

                    Seq.tryFindIndex
                        (fun (txOut: TxOut) ->
                            txOut.ScriptPubKey = toLocalWitScriptPubKey
                        )
                        commitTx.Outputs

                let! toLocalIndex =
                    match toLocalIndexOpt with
                    | Some toLocalIndex -> Ok toLocalIndex
                    | None -> Error BalanceBelowDustLimit

                let delayedPaymentPrivKey =
                    perCommitmentPoint.DeriveDelayedPaymentPrivKey
                        localChannelPrivKeys.DelayedPaymentBasepointSecret

                transactionBuilder
                    .SetVersion(TxVersionNumberOfCommitmentTxs)
                    .Extensions.Add(CommitmentToLocalExtension())

                return
                    transactionBuilder
                        .AddKeys(delayedPaymentPrivKey.RawKey())
                        .AddCoin(
                            ScriptCoin(
                                commitTx,
                                uint32 toLocalIndex,
                                toLocalScriptPubKey
                            ),
                            CoinOptions(
                                Sequence =
                                    (Nullable
                                     <| Sequence(
                                         uint32
                                             staticChannelConfig.RemoteParams.ToSelfDelay.Value
                                     ))
                            )
                        )
            }

        let ClaimCommitTxOutputs
            (closingTx: Transaction)
            (staticChannelConfig: StaticChannelConfig)
            (channelPrivKeys: ChannelPrivKeys)
            =
            let obscuredCommitmentNumberRes =
                tryGetObscuredCommitmentNumber
                    staticChannelConfig.FundingScriptCoin.Outpoint
                    closingTx

            match obscuredCommitmentNumberRes with
            | Ok obscuredCommitmentNumber ->
                let localChannelPubKeys = channelPrivKeys.ToChannelPubKeys()

                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                let commitmentNumber =
                    obscuredCommitmentNumber.Unobscure
                        staticChannelConfig.IsFunder
                        localChannelPubKeys.PaymentBasepoint
                        remoteChannelPubKeys.PaymentBasepoint

                {
                    MainOutput =
                        ClaimMainOutput
                            closingTx
                            commitmentNumber
                            staticChannelConfig
                            channelPrivKeys
                    AnchorOutput =
                        ClaimAnchorOutput
                            closingTx
                            staticChannelConfig
                            channelPrivKeys
                }
            | _ ->
                {
                    MainOutput = Error UnknownClosingTx
                    AnchorOutput = Error UnknownClosingTx
                }

        let internal unresolvedHtlcList
            (closingTx: Transaction)
            (localCommit: LocalCommit)
            (staticChannelConfig: StaticChannelConfig)
            (hash2preimage: PaymentHash -> option<PaymentPreimage>) //FIXME: should we check ProposedLocalChanges instead?
            =
            assert
                (closingTx.GetTxId() = localCommit.PublishableTxs.CommitTx.Value.GetTxId
                                           ())

            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let perCommitmentPoint = localCommit.PerCommitmentPoint

            let localCommitmentPubKeys =
                let localChannelPubKeys =
                    staticChannelConfig.LocalChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    false

            let remoteCommitmentPubKeys =
                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    remoteChannelPubKeys
                    staticChannelConfig.Type
                    true

            let unresolvedOutgoingHtlcs =
                localCommit.Spec.OutgoingHTLCs
                |> Map.toList
                |> List.choose(fun (_id, htlcAddMsg) ->
                    let redeem =
                        Scripts.htlcOffered
                            localCommitmentPubKeys.HtlcPubKey
                            remoteCommitmentPubKeys.HtlcPubKey
                            remoteCommitmentPubKeys.RevocationPubKey
                            htlcAddMsg.PaymentHash
                            commitmentFormat.HtlcCsvLock

                    let spk = redeem.WitHash.ScriptPubKey

                    let outputExistsInCommitmentTx =
                        closingTx.Outputs
                        |> Seq.exists(fun output -> output.ScriptPubKey = spk)

                    if outputExistsInCommitmentTx then
                        Some(
                            HtlcTransaction.Timeout(
                                htlcAddMsg.HTLCId,
                                spk,
                                htlcAddMsg.CLTVExpiry.Value,
                                htlcAddMsg.Amount
                            )
                        )
                    else
                        None
                )

            let unresolvedIncomingHtlcs =
                localCommit.Spec.IncomingHTLCs
                |> Map.toList
                |> List.choose(fun (_id, htlcAddMsg) ->
                    match hash2preimage htlcAddMsg.PaymentHash with
                    | Some preimage ->
                        let redeem =
                            Scripts.htlcReceived
                                localCommitmentPubKeys.HtlcPubKey
                                remoteCommitmentPubKeys.HtlcPubKey
                                remoteCommitmentPubKeys.RevocationPubKey
                                htlcAddMsg.PaymentHash
                                htlcAddMsg.CLTVExpiry.Value
                                commitmentFormat.HtlcCsvLock

                        let spk = redeem.WitHash.ScriptPubKey

                        let outputExistsInCommitmentTx =
                            closingTx.Outputs
                            |> Seq.exists(fun output ->
                                output.ScriptPubKey = spk
                            )

                        if outputExistsInCommitmentTx then
                            Some(
                                HtlcTransaction.Success(
                                    htlcAddMsg.HTLCId,
                                    spk,
                                    preimage,
                                    htlcAddMsg.Amount
                                )
                            )
                        else
                            None
                    | None -> None
                )

            unresolvedIncomingHtlcs @ unresolvedOutgoingHtlcs

        let internal claimHtlcOutput
            (htlcInfo: HtlcTransaction)
            (closingTx: Transaction)
            (localCommit: LocalCommit)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =
            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let perCommitmentPoint = localCommit.PerCommitmentPoint
            let localChannelPubKeys = localChannelPrivKeys.ToChannelPubKeys()

            let localCommitmentPubKeys =
                perCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    false

            let remoteCommitmentPubKeys =
                perCommitmentPoint.DeriveCommitmentPubKeys
                    staticChannelConfig.RemoteChannelPubKeys
                    staticChannelConfig.Type
                    true

            let htlcPrivKey =
                perCommitmentPoint.DeriveHtlcPrivKey
                    localChannelPrivKeys.HtlcBasepointSecret

            let dest =
                Scripts.toLocalDelayed
                    remoteCommitmentPubKeys.RevocationPubKey
                    staticChannelConfig.RemoteParams.ToSelfDelay
                    localCommitmentPubKeys.DelayedPaymentPubKey

            match htlcInfo with
            | Timeout(htlcId, _, _, _) ->
                let htlcAddMsg =
                    localCommit.Spec.OutgoingHTLCs |> Map.find htlcId

                let remoteSignature =
                    localCommit.OutgoingHtlcTxRemoteSigs |> Map.find htlcId

                let redeem =
                    Scripts.htlcOffered
                        localCommitmentPubKeys.HtlcPubKey
                        remoteCommitmentPubKeys.HtlcPubKey
                        remoteCommitmentPubKeys.RevocationPubKey
                        htlcAddMsg.PaymentHash
                        commitmentFormat.HtlcCsvLock

                let spk = redeem.WitHash.ScriptPubKey

                let txIn = findScriptPubKey closingTx spk

                let txb =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let scriptCoin = ScriptCoin(txIn, redeem)
                // we have already done dust limit check above
                txb.DustPrevention <- false
                txb.Extensions.Add(HtlcOfferedExtension None)

                txb
                    .AddCoin(
                        scriptCoin,
                        CoinOptions(
                            Sequence =
                                (Nullable
                                 <| Sequence
                                     commitmentFormat.HtlcTxInputSequence)
                        )
                    )
                    .Send(dest.WitHash, htlcAddMsg.Amount.ToMoney())
                    .AddKnownSignature(
                        remoteCommitmentPubKeys.HtlcPubKey.RawPubKey(),
                        remoteSignature,
                        scriptCoin.Outpoint
                    )
                    .AddKeys(htlcPrivKey.RawKey())
                    .SetVersion(2u)
                    .SetLockTime(!>htlcAddMsg.CLTVExpiry.Value)
                |> ignore<TransactionBuilder>

                txb, true
            | Success(htlcId, _, preImage, _) ->
                let htlcAddMsg =
                    localCommit.Spec.IncomingHTLCs |> Map.find htlcId

                let remoteSignature =
                    localCommit.IncomingHtlcTxRemoteSigs |> Map.find htlcId

                let redeem =
                    Scripts.htlcReceived
                        localCommitmentPubKeys.HtlcPubKey
                        remoteCommitmentPubKeys.HtlcPubKey
                        remoteCommitmentPubKeys.RevocationPubKey
                        htlcAddMsg.PaymentHash
                        htlcAddMsg.CLTVExpiry.Value
                        commitmentFormat.HtlcCsvLock

                let spk = redeem.WitHash.ScriptPubKey

                let txIn = findScriptPubKey closingTx spk

                let txb =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let scriptCoin = ScriptCoin(txIn, redeem)
                // we have already done dust limit check above
                txb.DustPrevention <- false
                txb.Extensions.Add(HtlcReceivedExtension(Some preImage))

                txb
                    .AddCoin(
                        scriptCoin,
                        CoinOptions(
                            Sequence =
                                (Nullable
                                 <| Sequence
                                     commitmentFormat.HtlcTxInputSequence)
                        )
                    )
                    .Send(dest.WitHash, htlcAddMsg.Amount.ToMoney())
                    .AddKnownSignature(
                        remoteCommitmentPubKeys.HtlcPubKey.RawPubKey(),
                        remoteSignature,
                        scriptCoin.Outpoint
                    )
                    .AddKeys(htlcPrivKey.RawKey())
                    .SetVersion(TxVersionNumberOfCommitmentTxs)
                |> ignore<TransactionBuilder>

                txb, true
            | Penalty _ ->
                failwith
                    "Should not happen because only RevokedClose.UnresolvedHtlcList uses `Penalty` case"

        let internal claimDelayedHtlcTx
            (spendingTx: Transaction)
            (localCommit: LocalCommit)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =

            let perCommitmentPoint = localCommit.PerCommitmentPoint

            let localCommitmentPubKeys =
                let localChannelPubKeys =
                    staticChannelConfig.LocalChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    false

            let remoteCommitmentPubKeys =
                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                perCommitmentPoint.DeriveCommitmentPubKeys
                    remoteChannelPubKeys
                    staticChannelConfig.Type
                    true

            let delayedPrivKey =
                perCommitmentPoint.DeriveDelayedPaymentPrivKey
                    localChannelPrivKeys.DelayedPaymentBasepointSecret

            let redeem =
                Scripts.toLocalDelayed
                    remoteCommitmentPubKeys.RevocationPubKey
                    staticChannelConfig.RemoteParams.ToSelfDelay
                    localCommitmentPubKeys.DelayedPaymentPubKey

            let spk = redeem.WitHash.ScriptPubKey

            let outputsToSpend =
                spendingTx.Outputs.AsIndexedOutputs()
                |> Seq.where(fun out -> out.TxOut.ScriptPubKey = spk)
                |> Seq.map(fun out -> ScriptCoin(out.ToCoin(), redeem) :> ICoin)
                |> Seq.toArray

            if not(Seq.isEmpty outputsToSpend) then
                let txb =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                txb.Extensions.Add(CommitmentToLocalExtension())

                outputsToSpend
                |> Seq.iter(fun output ->
                    txb.AddCoin(
                        output,
                        CoinOptions(
                            Sequence =
                                (Nullable
                                 <| Sequence(
                                     uint32
                                         staticChannelConfig.RemoteParams.ToSelfDelay.Value
                                 ))
                        )
                    )
                    |> ignore<TransactionBuilder>
                )

                txb
                    .AddKeys(delayedPrivKey.RawKey())
                    .SetVersion(TxVersionNumberOfCommitmentTxs)
                |> ignore<TransactionBuilder>

                Some txb
            else
                None

    module RevokedClose =
        let private ClaimMainOutput
            (closingTx: Transaction)
            (commitmentNumber: CommitmentNumber)
            (staticChannelConfig: StaticChannelConfig)
            (remotePerCommitmentSecret: Choice<PerCommitmentSecret, PerCommitmentSecretStore>)
            (localChannelPrivKeys: ChannelPrivKeys)
            : Result<TransactionBuilder, OutputClaimError> =
            result {
                let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

                let localChannelPubKeys =
                    localChannelPrivKeys.ToChannelPubKeys()

                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                let! perCommitmentSecret =
                    match remotePerCommitmentSecret with
                    | Choice1Of2 remotePerCommitmentSecret ->
                        Ok remotePerCommitmentSecret
                    | Choice2Of2 remotePerCommitmentSecretStore ->
                        let commitmentSecretOpt =
                            remotePerCommitmentSecretStore.GetPerCommitmentSecret
                                commitmentNumber

                        match commitmentSecretOpt with
                        | Some commitmentSecret -> Ok commitmentSecret
                        | None -> Error OutputClaimError.UnknownClosingTx

                let perCommitmentPoint =
                    perCommitmentSecret.PerCommitmentPoint()

                let localCommitmentPubKeys =
                    perCommitmentPoint.DeriveCommitmentPubKeys
                        localChannelPubKeys
                        staticChannelConfig.Type
                        true

                let remoteCommitmentPubKeys =
                    perCommitmentPoint.DeriveCommitmentPubKeys
                        remoteChannelPubKeys
                        staticChannelConfig.Type
                        false

                let transactionBuilder =
                    Transactions.createDeterministicTransactionBuilder
                        staticChannelConfig.Network

                let toRemoteScriptPubKey =
                    match commitmentFormat with
                    | DefaultCommitmentFormat ->
                        localCommitmentPubKeys
                            .PaymentPubKey
                            .RawPubKey()
                            .WitHash
                            .ScriptPubKey
                    | AnchorCommitmentFormat ->
                        (Scripts.toRemoteDelayed
                            localCommitmentPubKeys.PaymentPubKey)
                            .WitHash
                            .ScriptPubKey

                let toLocalScriptPubKey =
                    Scripts.toLocalDelayed
                        localCommitmentPubKeys.RevocationPubKey
                        staticChannelConfig.LocalParams.ToSelfDelay
                        remoteCommitmentPubKeys.DelayedPaymentPubKey

                let toLocalWitScriptPubKey =
                    toLocalScriptPubKey.WitHash.ScriptPubKey

                let toRemoteIndexOpt =
                    closingTx.Outputs
                    |> Seq.tryFindIndex(fun out ->
                        out.ScriptPubKey = toRemoteScriptPubKey
                    )

                toRemoteIndexOpt
                |> Option.iter(fun toRemoteIndex ->
                    let localPaymentPrivKey =
                        perCommitmentPoint.DerivePaymentPrivKey
                            localChannelPrivKeys.PaymentBasepointSecret
                            staticChannelConfig.Type
                            true

                    transactionBuilder.SetVersion TxVersionNumberOfCommitmentTxs
                    |> ignore<TransactionBuilder>

                    transactionBuilder.AddKeys(localPaymentPrivKey.RawKey())
                    |> ignore<TransactionBuilder>

                    match commitmentFormat with
                    | DefaultCommitmentFormat ->
                        transactionBuilder.AddCoin(
                            Coin(closingTx, toRemoteIndex |> uint32)
                        )
                    | AnchorCommitmentFormat ->
                        transactionBuilder.Extensions.Add(
                            CommitmentToDelayedRemoteExtension()
                        )

                        let redeem =
                            Scripts.toRemoteDelayed
                                localCommitmentPubKeys.PaymentPubKey

                        transactionBuilder.AddCoin(
                            ScriptCoin(closingTx, uint32 toRemoteIndex, redeem),
                            CoinOptions(Sequence = (Nullable <| Sequence 1u))
                        )
                    |> ignore
                )

                let toLocalIndexOpt =
                    closingTx.Outputs
                    |> Seq.tryFindIndex(fun out ->
                        out.ScriptPubKey = toLocalWitScriptPubKey
                    )

                toLocalIndexOpt
                |> Option.iter(fun toLocalIndex ->
                    let revocationPrivKey =
                        perCommitmentSecret.DeriveRevocationPrivKey
                            localChannelPrivKeys.RevocationBasepointSecret

                    transactionBuilder.Extensions.Add(
                        CommitmentToLocalExtension()
                    )

                    transactionBuilder
                        .AddKeys(revocationPrivKey.RawKey())
                        .AddCoin(
                            ScriptCoin(
                                closingTx,
                                toLocalIndex |> uint32,
                                toLocalScriptPubKey
                            )
                        )
                    |> ignore
                )

                // We should've retuned BalanceBelowDustLimit here
                // but because it's possible for old local commitment TXs to
                // get used with HandleFundingTxSpent (which calls
                // RevokedClose.ClaimMainOutput for all non-last
                // commitment txs) we can't return BalanceBelowDustLimit error
                // and we instead use UnknownClosingTx error.
                // There's a small edge case: all the commitment tx money
                // to be in HTLCs (which we should return BalanceBelowDustLimit
                // for) but we return an invalid error msg.
                if toLocalIndexOpt.IsNone && toRemoteIndexOpt.IsNone then
                    return! Error UnknownClosingTx
                else
                    return transactionBuilder
            }

        let createPenaltyTx
            (localChannelPrivKeys: ChannelPrivKeys)
            (staticChannelConfig: StaticChannelConfig)
            (remoteCommit: RemoteCommit)
            (remotePerCommitmentSecret: PerCommitmentSecret)
            =
            let localChannelPubKeys = localChannelPrivKeys.ToChannelPubKeys()

            let remotePerCommitmentPoint =
                remotePerCommitmentSecret.PerCommitmentPoint()

            let localCommitmentPubKeys =
                remotePerCommitmentPoint.DeriveCommitmentPubKeys
                    localChannelPubKeys
                    staticChannelConfig.Type
                    true

            let remoteCommitmentPubKeys =
                remotePerCommitmentPoint.DeriveCommitmentPubKeys
                    staticChannelConfig.RemoteChannelPubKeys
                    staticChannelConfig.Type
                    false

            //Reconstruct the remote commitment tx for the given remoteCommit
            let commitTx =
                Transactions.makeCommitTx
                    staticChannelConfig.FundingScriptCoin
                    remoteCommit.Index
                    staticChannelConfig.RemoteChannelPubKeys.PaymentBasepoint
                    localChannelPubKeys.PaymentBasepoint
                    (not staticChannelConfig.IsFunder)
                    (staticChannelConfig.RemoteParams.DustLimitSatoshis)
                    localCommitmentPubKeys.RevocationPubKey
                    staticChannelConfig.LocalParams.ToSelfDelay
                    remoteCommitmentPubKeys.DelayedPaymentPubKey
                    localCommitmentPubKeys.PaymentPubKey
                    remoteCommitmentPubKeys.HtlcPubKey
                    localCommitmentPubKeys.HtlcPubKey
                    staticChannelConfig.RemoteChannelPubKeys.FundingPubKey
                    localChannelPubKeys.FundingPubKey
                    remoteCommit.Spec
                    staticChannelConfig.Type.CommitmentFormat
                    staticChannelConfig.Network

            ClaimMainOutput
                (commitTx.Value.GetGlobalTransaction())
                remoteCommit.Index
                staticChannelConfig
                (Choice1Of2 remotePerCommitmentSecret)
                localChannelPrivKeys

        let ClaimCommitTxOutputs
            (closingTx: Transaction)
            (staticChannelConfig: StaticChannelConfig)
            (remotePerCommitmentSecrets: PerCommitmentSecretStore)
            (channelPrivKeys: ChannelPrivKeys)
            =
            let obscuredCommitmentNumberRes =
                tryGetObscuredCommitmentNumber
                    staticChannelConfig.FundingScriptCoin.Outpoint
                    closingTx

            match obscuredCommitmentNumberRes with
            | Ok obscuredCommitmentNumber ->
                let localChannelPubKeys = channelPrivKeys.ToChannelPubKeys()

                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                let commitmentNumber =
                    obscuredCommitmentNumber.Unobscure
                        staticChannelConfig.IsFunder
                        localChannelPubKeys.PaymentBasepoint
                        remoteChannelPubKeys.PaymentBasepoint

                let claimMainOutputsRes =
                    ClaimMainOutput
                        closingTx
                        commitmentNumber
                        staticChannelConfig
                        (Choice2Of2 remotePerCommitmentSecrets)
                        channelPrivKeys

                match claimMainOutputsRes with
                | Error OutputClaimError.UnknownClosingTx ->
                    {
                        MainOutput = Error OutputClaimError.UnknownClosingTx
                        AnchorOutput = Error OutputClaimError.UnknownClosingTx
                    }
                | claimMainOutput ->
                    {
                        MainOutput = claimMainOutput
                        AnchorOutput = Error Inapplicable
                    }
            | _ ->
                {
                    MainOutput = Error UnknownClosingTx
                    AnchorOutput = Error UnknownClosingTx
                }

        let UnresolvedHtlcList
            (closingTx: Transaction)
            (savedChannelState: SavedChannelState)
            =
            let staticChannelConfig = savedChannelState.StaticChannelConfig
            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let remoteCommitOpt =
                savedChannelState.HistoricalRemoteCommits
                |> Map.tryFind(closingTx.GetTxId().Value.ToString())

            match remoteCommitOpt with
            | Some remoteCommit ->
                let perCommitmentPoint = remoteCommit.RemotePerCommitmentPoint

                let localCommitmentPubKeys =
                    let localChannelPubKeys =
                        staticChannelConfig.LocalChannelPubKeys

                    perCommitmentPoint.DeriveCommitmentPubKeys
                        localChannelPubKeys
                        staticChannelConfig.Type
                        true

                let remoteCommitmentPubKeys =
                    let remoteChannelPubKeys =
                        staticChannelConfig.RemoteChannelPubKeys

                    perCommitmentPoint.DeriveCommitmentPubKeys
                        remoteChannelPubKeys
                        staticChannelConfig.Type
                        false

                let unresolvedOutgoingHtlcs =
                    remoteCommit.Spec.OutgoingHTLCs
                    |> Map.toList
                    |> List.choose(fun (_id, htlcAddMsg) ->
                        let redeem =
                            Scripts.htlcOffered
                                remoteCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.RevocationPubKey
                                htlcAddMsg.PaymentHash
                                commitmentFormat.HtlcCsvLock

                        let spk = redeem.WitHash.ScriptPubKey

                        let outputExistsInCommitmentTx =
                            closingTx.Outputs
                            |> Seq.exists(fun output ->
                                output.ScriptPubKey = spk
                            )

                        if outputExistsInCommitmentTx then
                            Some(
                                HtlcTransaction.Penalty(
                                    redeem,
                                    htlcAddMsg.Amount
                                )
                            )
                        else
                            None
                    )

                let unresolvedIncomingHtlcs =
                    remoteCommit.Spec.IncomingHTLCs
                    |> Map.toList
                    |> List.choose(fun (_id, htlcAddMsg) ->
                        let redeem =
                            Scripts.htlcReceived
                                remoteCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.HtlcPubKey
                                localCommitmentPubKeys.RevocationPubKey
                                htlcAddMsg.PaymentHash
                                htlcAddMsg.CLTVExpiry.Value
                                commitmentFormat.HtlcCsvLock

                        let spk = redeem.WitHash.ScriptPubKey

                        let outputExistsInCommitmentTx =
                            closingTx.Outputs
                            |> Seq.exists(fun output ->
                                output.ScriptPubKey = spk
                            )

                        if outputExistsInCommitmentTx then
                            Some(
                                HtlcTransaction.Penalty(
                                    redeem,
                                    htlcAddMsg.Amount
                                )
                            )
                        else
                            None
                    )

                unresolvedOutgoingHtlcs @ unresolvedIncomingHtlcs
            | None -> List.empty

        let ClaimHtlcOutput
            (htlcInfo: HtlcTransaction)
            (closingTx: Transaction)
            (remotePerCommitmentSecretStore: PerCommitmentSecretStore)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =
            let commitmentFormat = staticChannelConfig.Type.CommitmentFormat

            let obscuredCommitmentNumberRes =
                tryGetObscuredCommitmentNumber
                    staticChannelConfig.FundingScriptCoin.Outpoint
                    closingTx

            match obscuredCommitmentNumberRes with
            | Ok obscuredCommitmentNumber ->
                let localChannelPubKeys =
                    staticChannelConfig.LocalChannelPubKeys

                let remoteChannelPubKeys =
                    staticChannelConfig.RemoteChannelPubKeys

                let commitmentNumber =
                    obscuredCommitmentNumber.Unobscure
                        staticChannelConfig.IsFunder
                        localChannelPubKeys.PaymentBasepoint
                        remoteChannelPubKeys.PaymentBasepoint

                let perCommitmentSecret =
                    let commitmentSecretOpt =
                        remotePerCommitmentSecretStore.GetPerCommitmentSecret
                            commitmentNumber

                    match commitmentSecretOpt with
                    | Some commitmentSecret -> commitmentSecret
                    | None ->
                        failwithf
                            "Could not find commitment secret for commitment number %d"
                            (commitmentNumber.Index().UInt64)

                let revocationPrivKey =
                    perCommitmentSecret.DeriveRevocationPrivKey
                        localChannelPrivKeys.RevocationBasepointSecret

                match htlcInfo with
                | Penalty(redeemScript, _) ->
                    let spk = redeemScript.WitHash.ScriptPubKey
                    let txIn = findScriptPubKey closingTx spk

                    let txb =
                        Transactions.createDeterministicTransactionBuilder
                            staticChannelConfig.Network

                    let scriptCoin = ScriptCoin(txIn, redeemScript)
                    // we have already done dust limit check above
                    txb.DustPrevention <- false
                    txb.Extensions.Add(HtlcReceivedExtension None)
                    txb.Extensions.Add(HtlcOfferedExtension None)

                    txb
                        .AddCoin(
                            scriptCoin,
                            CoinOptions(
                                Sequence =
                                    (Nullable
                                     <| Sequence
                                         commitmentFormat.HtlcTxInputSequence)
                            )
                        )
                        .AddKeys(revocationPrivKey.RawKey())
                        .SetVersion(2u)
                    |> ignore<TransactionBuilder>

                    txb, false
                | _ ->
                    failwith
                        "We shouldn't have non-penalty HtlcTransaction here"
            | Error _ -> failwith "Invalid closing tx"

        let internal claimDelayedHtlcTx
            (spendingTx: Transaction)
            (remoteCommit: RemoteCommit)
            (remotePerCommitmentSecretStore: PerCommitmentSecretStore)
            (staticChannelConfig: StaticChannelConfig)
            (localChannelPrivKeys: ChannelPrivKeys)
            =

            let perCommitmentSecretOpt =
                let commitmentSecretOpt =
                    remotePerCommitmentSecretStore.GetPerCommitmentSecret
                        remoteCommit.Index

                match commitmentSecretOpt with
                | Some commitmentSecret -> Some commitmentSecret
                | None -> None

            match perCommitmentSecretOpt with
            | Some perCommitmentSecret ->
                let perCommitmentPoint =
                    perCommitmentSecret.PerCommitmentPoint()

                let localCommitmentPubKeys =
                    let localChannelPubKeys =
                        staticChannelConfig.LocalChannelPubKeys

                    perCommitmentPoint.DeriveCommitmentPubKeys
                        localChannelPubKeys
                        staticChannelConfig.Type
                        true

                let remoteCommitmentPubKeys =
                    let remoteChannelPubKeys =
                        staticChannelConfig.RemoteChannelPubKeys

                    perCommitmentPoint.DeriveCommitmentPubKeys
                        remoteChannelPubKeys
                        staticChannelConfig.Type
                        false

                let revocationPrivKey =
                    perCommitmentSecret.DeriveRevocationPrivKey
                        localChannelPrivKeys.RevocationBasepointSecret

                let redeem =
                    Scripts.toLocalDelayed
                        localCommitmentPubKeys.RevocationPubKey
                        staticChannelConfig.LocalParams.ToSelfDelay
                        remoteCommitmentPubKeys.DelayedPaymentPubKey

                let spk = redeem.WitHash.ScriptPubKey

                let outputsToSpend =
                    spendingTx.Outputs.AsIndexedOutputs()
                    |> Seq.where(fun out -> out.TxOut.ScriptPubKey = spk)
                    |> Seq.map(fun out ->
                        ScriptCoin(out.ToCoin(), redeem) :> ICoin
                    )
                    |> Seq.toArray

                if not(Seq.isEmpty outputsToSpend) then
                    let txb =
                        Transactions.createDeterministicTransactionBuilder
                            staticChannelConfig.Network

                    txb.Extensions.Add(CommitmentToLocalExtension())

                    outputsToSpend
                    |> Seq.iter(fun output ->
                        txb.AddCoin(output) |> ignore<TransactionBuilder>
                    )

                    txb
                        .AddKeys(revocationPrivKey.RawKey())
                        .SetVersion(TxVersionNumberOfCommitmentTxs)
                    |> ignore<TransactionBuilder>

                    Some txb
                else
                    None
            | None -> None

    let HandleFundingTxSpent
        (savedChannelState: SavedChannelState)
        (remoteNextCommitInfoOpt: Option<RemoteNextCommitInfo>)
        (channelPrivKeys: ChannelPrivKeys)
        (closingTx: Transaction)
        : ClosingResult =
        let closingTxId = closingTx.GetTxId()

        if savedChannelState.RemoteCurrentPerCommitmentPoint.IsSome then
            RemoteClose.ClaimCommitTxOutputs
                closingTx
                savedChannelState.StaticChannelConfig
                channelPrivKeys
                savedChannelState.RemoteCommit
                savedChannelState.RemoteCurrentPerCommitmentPoint
        elif closingTxId = savedChannelState.LocalCommit.PublishableTxs.CommitTx.Value.GetTxId
                               () then
            LocalClose.ClaimCommitTxOutputs
                closingTx
                savedChannelState.StaticChannelConfig
                channelPrivKeys
        elif
            savedChannelState.HistoricalLocalCommits.ContainsKey
                (closingTxId.Value.ToString())
        then
            LocalClose.ClaimCommitTxOutputs
                closingTx
                savedChannelState.StaticChannelConfig
                channelPrivKeys
        elif closingTxId = savedChannelState.RemoteCommit.TxId then
            RemoteClose.ClaimCommitTxOutputs
                closingTx
                savedChannelState.StaticChannelConfig
                channelPrivKeys
                savedChannelState.RemoteCommit
                None
        else
            match remoteNextCommitInfoOpt with
            | Some(Waiting waitingForRevokation) when
                closingTxId = waitingForRevokation.NextRemoteCommit.TxId
                ->
                RemoteClose.ClaimCommitTxOutputs
                    closingTx
                    savedChannelState.StaticChannelConfig
                    channelPrivKeys
                    waitingForRevokation.NextRemoteCommit
                    None
            | _ ->
                RevokedClose.ClaimCommitTxOutputs
                    closingTx
                    savedChannelState.StaticChannelConfig
                    savedChannelState.RemotePerCommitmentSecrets
                    channelPrivKeys

    let UnresolvedHtlcList
        (savedChannelState: SavedChannelState)
        (remoteNextCommitInfoOpt: Option<RemoteNextCommitInfo>)
        (closingTx: Transaction)
        hash2preimage
        =
        let closingTxId = closingTx.GetTxId()

        if savedChannelState.LocalCommit.PublishableTxs.CommitTx.Value.GetTxId() = closingTxId then
            LocalClose.unresolvedHtlcList
                closingTx
                savedChannelState.LocalCommit
                savedChannelState.StaticChannelConfig
                hash2preimage
        elif
            savedChannelState.HistoricalLocalCommits.ContainsKey
                (closingTxId.Value.ToString())
        then
            let localCommit =
                savedChannelState.HistoricalLocalCommits
                |> Map.find(closingTxId.Value.ToString())

            LocalClose.unresolvedHtlcList
                closingTx
                localCommit
                savedChannelState.StaticChannelConfig
                hash2preimage
        elif closingTxId = savedChannelState.RemoteCommit.TxId then
            RemoteClose.UnresolvedHtlcList
                closingTx
                savedChannelState.RemoteCommit
                savedChannelState.StaticChannelConfig
                hash2preimage
        else
            match remoteNextCommitInfoOpt with
            | Some(Waiting waitingForRevokation) when
                closingTxId = waitingForRevokation.NextRemoteCommit.TxId
                ->
                RemoteClose.UnresolvedHtlcList
                    closingTx
                    waitingForRevokation.NextRemoteCommit
                    savedChannelState.StaticChannelConfig
                    hash2preimage
            | _ -> RevokedClose.UnresolvedHtlcList closingTx savedChannelState

    let ClaimHtlcOutput
        (htlcInfo: HtlcTransaction)
        (savedChannelState: SavedChannelState)
        (remoteNextCommitInfoOpt: Option<RemoteNextCommitInfo>)
        (closingTx: Transaction)
        (localChannelPrivKeys: ChannelPrivKeys)
        =
        let closingTxId = closingTx.GetTxId()

        if savedChannelState.LocalCommit.PublishableTxs.CommitTx.Value.GetTxId() = closingTxId then
            LocalClose.claimHtlcOutput
                htlcInfo
                closingTx
                savedChannelState.LocalCommit
                savedChannelState.StaticChannelConfig
                localChannelPrivKeys
        elif
            savedChannelState.HistoricalLocalCommits.ContainsKey
                (closingTxId.Value.ToString())
        then
            let localCommit =
                savedChannelState.HistoricalLocalCommits
                |> Map.find(closingTxId.Value.ToString())

            LocalClose.claimHtlcOutput
                htlcInfo
                closingTx
                localCommit
                savedChannelState.StaticChannelConfig
                localChannelPrivKeys
        elif closingTxId = savedChannelState.RemoteCommit.TxId then
            RemoteClose.ClaimHtlcOutput
                htlcInfo
                closingTx
                savedChannelState.RemoteCommit
                savedChannelState.StaticChannelConfig
                localChannelPrivKeys
        else
            match remoteNextCommitInfoOpt with
            | Some(Waiting waitingForRevokation) when
                closingTxId = waitingForRevokation.NextRemoteCommit.TxId
                ->
                RemoteClose.ClaimHtlcOutput
                    htlcInfo
                    closingTx
                    waitingForRevokation.NextRemoteCommit
                    savedChannelState.StaticChannelConfig
                    localChannelPrivKeys
            | _ ->
                RevokedClose.ClaimHtlcOutput
                    htlcInfo
                    closingTx
                    savedChannelState.RemotePerCommitmentSecrets
                    savedChannelState.StaticChannelConfig
                    localChannelPrivKeys

    let ClaimDelayedHtlcTx
        (closingTx: Transaction)
        (spendingTx: Transaction)
        (savedChannelState: SavedChannelState)
        (remoteNextCommitInfoOpt: Option<RemoteNextCommitInfo>)
        (localChannelPrivKeys: ChannelPrivKeys)
        =
        let closingTxId = closingTx.GetTxId()

        if savedChannelState.LocalCommit.PublishableTxs.CommitTx.Value.GetTxId() = closingTxId then
            LocalClose.claimDelayedHtlcTx
                spendingTx
                savedChannelState.LocalCommit
                savedChannelState.StaticChannelConfig
                localChannelPrivKeys
        elif
            savedChannelState.HistoricalLocalCommits.ContainsKey
                (closingTxId.Value.ToString())
        then
            let localCommit =
                savedChannelState.HistoricalLocalCommits
                |> Map.find(closingTxId.Value.ToString())

            LocalClose.claimDelayedHtlcTx
                spendingTx
                localCommit
                savedChannelState.StaticChannelConfig
                localChannelPrivKeys
        elif closingTxId = savedChannelState.RemoteCommit.TxId then
            None
        else
            match remoteNextCommitInfoOpt with
            | Some(Waiting waitingForRevokation) when
                closingTxId = waitingForRevokation.NextRemoteCommit.TxId
                ->
                None
            | _ ->
                let remoteCommit =
                    savedChannelState.HistoricalRemoteCommits
                    |> Map.find(closingTxId.Value.ToString())

                RevokedClose.claimDelayedHtlcTx
                    spendingTx
                    remoteCommit
                    savedChannelState.RemotePerCommitmentSecrets
                    savedChannelState.StaticChannelConfig
                    localChannelPrivKeys
