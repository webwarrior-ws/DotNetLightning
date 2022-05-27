namespace DotNetLightning.Channel

open System

open NBitcoin
open NBitcoin.BuilderExtensions
open NBitcoin.Crypto
open DotNetLightning.Utils
open DotNetLightning.Crypto

open ResultUtils
open ResultUtils.Portability

type HtlcOfferedParameters =
    {
        RevocationPubKeyHash: array<byte>
        RemoteHtlcPubKey: HtlcPubKey
        LocalHtlcPubKey: HtlcPubKey
        PaymentHash: array<byte>
    }

    static member TryExtractParameters
        (scriptPubKey: Script)
        : Option<HtlcOfferedParameters> =
        let ops =
            scriptPubKey.ToOps()
            // we have to collect it into a list and convert back to a seq
            // because the IEnumerable that NBitcoin gives us is internally
            // mutable.
            |> List.ofSeq
            |> Seq.ofList

        let checkOpCode(opcodeType: OpcodeType) =
            seqParser<Op> { let! op = SeqParser.next()

            if op.Code = opcodeType then
                return ()
            else
                return! SeqParser.abort()
            }

        let parseResult =
            SeqParser.parse ops
            <| seqParser {
                do! checkOpCode OpcodeType.OP_DUP
                do! checkOpCode OpcodeType.OP_HASH160
                let! opRevocationPubKeyHash = SeqParser.next()

                let! revocationPubKeyHash =
                    seqParser {
                        if isNull opRevocationPubKeyHash.PushData then
                            return! SeqParser.abort()
                        else
                            try
                                return opRevocationPubKeyHash.PushData
                            with
                            | :? FormatException -> return! SeqParser.abort()
                    }

                do! checkOpCode OpcodeType.OP_EQUAL
                do! checkOpCode OpcodeType.OP_IF
                do! checkOpCode OpcodeType.OP_CHECKSIG
                do! checkOpCode OpcodeType.OP_ELSE
                let! opRemoteHtlcPubKey = SeqParser.next()

                let! remoteHtlcPubKey =
                    seqParser {
                        if isNull opRemoteHtlcPubKey.PushData then
                            return! SeqParser.abort()
                        else
                            try
                                return
                                    HtlcPubKey
                                    <| PubKey opRemoteHtlcPubKey.PushData
                            with
                            | :? FormatException -> return! SeqParser.abort()
                    }

                do! checkOpCode OpcodeType.OP_SWAP
                do! checkOpCode OpcodeType.OP_SIZE
                let! _shouldbe32 = SeqParser.next()
                do! checkOpCode OpcodeType.OP_EQUAL
                do! checkOpCode OpcodeType.OP_NOTIF
                do! checkOpCode OpcodeType.OP_DROP
                do! checkOpCode OpcodeType.OP_2
                do! checkOpCode OpcodeType.OP_SWAP
                let! opLocalHtlcPubKey = SeqParser.next()

                let! localHtlcPubKey =
                    seqParser {
                        if isNull opLocalHtlcPubKey.PushData then
                            return! SeqParser.abort()
                        else
                            try
                                return
                                    HtlcPubKey
                                    <| PubKey opLocalHtlcPubKey.PushData
                            with
                            | :? FormatException -> return! SeqParser.abort()
                    }

                do! checkOpCode OpcodeType.OP_2
                do! checkOpCode OpcodeType.OP_CHECKMULTISIG
                do! checkOpCode OpcodeType.OP_ELSE
                do! checkOpCode OpcodeType.OP_HASH160
                let! opPaymentHash = SeqParser.next()

                let! paymentHash =
                    seqParser {
                        if isNull opPaymentHash.PushData then
                            return! SeqParser.abort()
                        else
                            try
                                return opPaymentHash.PushData
                            with
                            | :? FormatException -> return! SeqParser.abort()
                    }

                do! checkOpCode OpcodeType.OP_EQUALVERIFY
                do! checkOpCode OpcodeType.OP_CHECKSIG
                do! checkOpCode OpcodeType.OP_ENDIF

                // we can't verify further because it changes based on anchor/non-anchor
                return
                    {
                        RevocationPubKeyHash = revocationPubKeyHash
                        RemoteHtlcPubKey = remoteHtlcPubKey
                        LocalHtlcPubKey = localHtlcPubKey
                        PaymentHash = paymentHash
                    }
            }

        match parseResult with
        | Ok data -> Some data
        | Error _consumeAllError -> None

type internal HtlcOfferedExtension(paymentPreimageOpt: option<PaymentPreimage>) =
    inherit BuilderExtension()

    override __.Match(coin: ICoin, _input: PSBTInput) : bool =
        (HtlcOfferedParameters.TryExtractParameters(coin.GetScriptCode()))
            .IsSome

    override __.Sign
        (
            inputSigningContext: InputSigningContext,
            keyRepo: IKeyRepository,
            signer: ISigner
        ) =
        let scriptPubKey = inputSigningContext.Coin.GetScriptCode()

        match
            HtlcOfferedParameters.TryExtractParameters scriptPubKey,
            paymentPreimageOpt
            with
        | Some parameters, Some _preImage ->
            match signer.Sign(parameters.RemoteHtlcPubKey.RawPubKey()) with
            | :? TransactionSignature as signature when not(isNull signature) ->
                inputSigningContext.Input.PartialSigs.AddOrReplace(
                    parameters.RemoteHtlcPubKey.RawPubKey(),
                    signature
                )
            | _ -> ()
        | Some parameters, None ->
            match keyRepo.FindKey scriptPubKey with
            | :? PubKey as revocationPubKey when not(isNull revocationPubKey) ->
                match signer.Sign revocationPubKey with
                | :? TransactionSignature as signature when
                    not(isNull signature)
                    ->
                    inputSigningContext.Input.PartialSigs.AddOrReplace(
                        revocationPubKey,
                        signature
                    )
                | _ -> ()
            | _ ->
                match signer.Sign(parameters.RemoteHtlcPubKey.RawPubKey()) with
                | :? TransactionSignature as remoteSignature when
                    not(isNull remoteSignature)
                    ->
                    match signer.Sign(parameters.LocalHtlcPubKey.RawPubKey())
                        with
                    | :? TransactionSignature as localSignature when
                        not(isNull localSignature)
                        ->
                        inputSigningContext.Input.PartialSigs.AddOrReplace(
                            parameters.RemoteHtlcPubKey.RawPubKey(),
                            remoteSignature
                        )

                        inputSigningContext.Input.PartialSigs.AddOrReplace(
                            parameters.LocalHtlcPubKey.RawPubKey(),
                            localSignature
                        )
                    | _ -> ()
                | _ -> ()
        | _ -> ()

    override __.CanDeduceScriptPubKey(_scriptSig: Script) : bool =
        false

    override __.DeduceScriptPubKey(_scriptSig: Script) : Script =
        raise <| NotSupportedException()

    override __.CanEstimateScriptSigSize(coin: ICoin) : bool =
        (HtlcOfferedParameters.TryExtractParameters(coin.GetScriptCode()))
            .IsSome

    override __.EstimateScriptSigSize(_coin: ICoin) : int =
        match paymentPreimageOpt with
        | Some _preimage ->
            ChannelConstants.MaxSignatureSize + PaymentPreimage.LENGTH
        | None -> (2 * ChannelConstants.MaxSignatureSize) + 2

    override __.IsCompatibleKey(pubKey: IPubKey, scriptPubKey: Script) : bool =
        match HtlcOfferedParameters.TryExtractParameters scriptPubKey with
        | None -> false
        | Some parameters ->
            match pubKey with
            | :? PubKey as pubKey ->
                Hashes.RIPEMD160(Hashes.SHA256(pubKey.ToBytes())) = parameters.RevocationPubKeyHash
            | _ -> false


    override __.Finalize(inputSigningContext: InputSigningContext) =
        let scriptPubKey = inputSigningContext.Coin.GetScriptCode()

        let parameters =
            match (HtlcOfferedParameters.TryExtractParameters scriptPubKey) with
            | Some parameters -> parameters
            | None ->
                failwith
                    "NBitcoin should not call this unless Match returns true"

        let txIn = inputSigningContext.Input

        match paymentPreimageOpt with
        | Some preImage ->
            if txIn.PartialSigs.Count <> 0 then
                let remoteSignatureOpt =
                    txIn.PartialSigs
                    |> Seq.tryFind(fun keySignature ->
                        keySignature.Key = parameters.RemoteHtlcPubKey.RawPubKey
                                               ()
                    )

                match remoteSignatureOpt with
                | Some remoteKeySignature ->
                    txIn.FinalScriptSig <-
                        Script
                            [
                                Op.GetPushOp(remoteKeySignature.Value.ToBytes())
                                Op.GetPushOp(Array.ofSeq preImage.Value)
                            ]
                | _ -> ()
        | None ->
            if txIn.PartialSigs.Count <> 0 then
                let remoteSignatureOpt =
                    txIn.PartialSigs
                    |> Seq.tryFind(fun keySignature ->
                        keySignature.Key = parameters.RemoteHtlcPubKey.RawPubKey
                                               ()
                    )

                let localSignatureOpt =
                    txIn.PartialSigs
                    |> Seq.tryFind(fun keySignature ->
                        keySignature.Key = parameters.LocalHtlcPubKey.RawPubKey
                                               ()
                    )

                let revocationSignatureOpt =
                    txIn.PartialSigs
                    |> Seq.tryFind(fun keySignature ->
                        Hashes.RIPEMD160(
                            Hashes.SHA256(keySignature.Key.ToBytes())
                        ) = parameters.RevocationPubKeyHash
                    )

                match
                    revocationSignatureOpt,
                    remoteSignatureOpt,
                    localSignatureOpt
                    with
                | Some revocationKeySignature, _, _ ->
                    txIn.FinalScriptSig <-
                        Script
                            [
                                Op.GetPushOp(
                                    revocationKeySignature.Value.ToBytes()
                                )
                                Op.GetPushOp(
                                    revocationKeySignature.Key.ToBytes()
                                )
                            ]
                | None, Some remoteKeySignature, Some localKeySignature ->
                    txIn.FinalScriptSig <-
                        Script
                            [
                                Op.op_Implicit OpcodeType.OP_0
                                Op.GetPushOp(remoteKeySignature.Value.ToBytes())
                                Op.GetPushOp(localKeySignature.Value.ToBytes())
                                Op.op_Implicit OpcodeType.OP_0
                            ]
                | _ -> ()
