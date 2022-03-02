namespace DotNetLightning.Channel

open System

open NBitcoin
open NBitcoin.BuilderExtensions
open DotNetLightning.Utils
open DotNetLightning.Crypto

open ResultUtils
open ResultUtils.Portability

type CommitmentAnchorParameters =
    {
        FundingPubKey: FundingPubKey
    }

    static member TryExtractParameters
        (scriptPubKey: Script)
        : Option<CommitmentAnchorParameters> =
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

        let parseToCompletionResult =
            SeqParser.parseToCompletion ops
            <| seqParser {
                let! opFundingPubKey = SeqParser.next()

                let! fundingPubKey =
                    seqParser {
                        if isNull opFundingPubKey.PushData then
                            return! SeqParser.abort()
                        else
                            try
                                return
                                    FundingPubKey
                                    <| PubKey opFundingPubKey.PushData
                            with
                            | :? FormatException -> return! SeqParser.abort()
                    }

                do! checkOpCode OpcodeType.OP_CHECKSIG
                do! checkOpCode OpcodeType.OP_IFDUP
                do! checkOpCode OpcodeType.OP_NOTIF
                do! checkOpCode OpcodeType.OP_16
                do! checkOpCode OpcodeType.OP_CHECKSEQUENCEVERIFY
                do! checkOpCode OpcodeType.OP_ENDIF

                return
                    {
                        FundingPubKey = fundingPubKey
                    }
            }

        match parseToCompletionResult with
        | Ok data -> Some data
        | Error _consumeAllError -> None

type internal CommitmentAnchorExtension() =
    inherit BuilderExtension()

    override __.Match(coin: ICoin, _input: PSBTInput) : bool =
        (CommitmentAnchorParameters.TryExtractParameters(coin.GetScriptCode()))
            .IsSome

    override __.Sign
        (
            inputSigningContext: InputSigningContext,
            keyRepo: IKeyRepository,
            signer: ISigner
        ) =
        let scriptPubKey = inputSigningContext.Coin.GetScriptCode()

        match keyRepo.FindKey scriptPubKey with
        | :? PubKey as pubKey when not(isNull pubKey) ->
            match signer.Sign pubKey with
            | :? TransactionSignature as signature when not(isNull signature) ->
                inputSigningContext.Input.PartialSigs.AddOrReplace(
                    pubKey,
                    signature
                )
            | _ -> ()
        | _ -> ()

    override __.CanDeduceScriptPubKey(_scriptSig: Script) : bool =
        false

    override __.DeduceScriptPubKey(_scriptSig: Script) : Script =
        raise <| NotSupportedException()

    override __.CanEstimateScriptSigSize(coin: ICoin) : bool =
        (CommitmentAnchorParameters.TryExtractParameters(coin.GetScriptCode()))
            .IsSome

    override __.EstimateScriptSigSize(_coin: ICoin) : int =
        ChannelConstants.MaxSignatureSize

    override __.IsCompatibleKey(pubKey: IPubKey, scriptPubKey: Script) : bool =
        match CommitmentAnchorParameters.TryExtractParameters scriptPubKey with
        | None -> false
        | Some parameters ->
            parameters.FundingPubKey.RawPubKey() :> IPubKey = pubKey


    override __.Finalize(inputSigningContext: InputSigningContext) =
        let scriptPubKey = inputSigningContext.Coin.GetScriptCode()

        let parameters =
            match (CommitmentAnchorParameters.TryExtractParameters scriptPubKey)
                with
            | Some parameters -> parameters
            | None ->
                failwith
                    "NBitcoin should not call this unless Match returns true"

        let txIn = inputSigningContext.Input

        if txIn.PartialSigs.Count <> 0 then
            let keyAndSignatureOpt = txIn.PartialSigs |> Seq.tryExactlyOne

            match keyAndSignatureOpt with
            | Some keyAndSignature when
                keyAndSignature.Key = parameters.FundingPubKey.RawPubKey()
                ->
                inputSigningContext.Input.FinalScriptSig <-
                    Script
                        [
                            Op.GetPushOp(keyAndSignature.Value.ToBytes())
                        ]
            | _ -> ()
