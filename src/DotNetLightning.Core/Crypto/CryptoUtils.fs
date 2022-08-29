namespace DotNetLightning.Crypto

open System
open NBitcoin // For e.g. uint256
open DotNetLightning.Utils
open NBitcoin.Crypto

#if BouncyCastle
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Crypto.Macs // For Poly1305
#else
open NBitcoin.Secp256k1
#endif

open ResultUtils
open ResultUtils.Portability


/// <namespacedoc>
///     <summary>
///     "DotNetLightning.Crypto" contains a cryptographic utilities to work with
///      LN. e.g.
///     1. Extension methods for key types to tweak/multiply
///         e.g. <c>NBitcoin.Key.Mul</c>
///     2. Aezeed <c>CipherSeed</c> for managing node master key in seed phrase with
///        its birthday encoded. (useful when rescanning the blockchain)
///        This is a port of the aezeed in lnd.
///     3. Sphinx packet decoding/encoding described in bolt04
///     4. <c>PerCommitmentSecretStore</c> to hold "per_commitment_secret" in an
///         efficient way.
///     </summary>
/// </namespacedoc>
/// <seealso href ="https://github.com/lightningnetwork/lnd/tree/master/aezeed">Aezeed in lnd </seealso>
/// <exclude />
module NamespaceDocDummy =
    ()

/// <summary>
///     An error on cryptography layer.
///     If this happens, normally you should close the connection against the peer.
///     Since it is clear protocol violation.
/// </summary>
type CryptoError =
    | BadMac
    | InvalidErrorPacketLength of expected: int * actual: int
    | InvalidPublicKey of array<byte>
    | InvalidMessageLength of int
    | FailedToParseErrorPacket of
        packet: array<byte> *
        sharedSecrets: list<(array<byte> * PubKey)>
    | InvalidPayloadLength

    member this.Message =
        match this with
        | BadMac -> "Bad MAC"
        | InvalidErrorPacketLength(expected, actual) ->
            sprintf
                "Invalid error packet length. Expected %i, got %i"
                expected
                actual
        | InvalidPublicKey publicKeyBytes ->
            sprintf "Invalid public key: %s" (publicKeyBytes.ToHexString())
        | InvalidMessageLength length ->
            sprintf "Invalid message length (%i)" length
        | InvalidPayloadLength -> "Invalid payload length"
        | FailedToParseErrorPacket _ -> "failed to parse error packet."

module Secret =
    let FromKeyPair(pub: PubKey, priv: Key) =
        let ba = pub.GetSharedPubkey(priv).ToBytes()
        Hashes.SHA256 ba

/// An interface responsible for set of low-level cryptographic operation.
/// We need this because there are several types of secp256k1 implementation
/// * 1. `NBitcoinSecp256k1`
///   * The one we usually want to use. Which depends on [NBitcoin's implementation](https://github.com/MetacoSA/NBitcoin/tree/master/NBitcoin.Secp256k1)
/// * 2. `BouncySecp256k1`
///   * Fallback when we are compiling with `netstandard2.0`, since `NBitcoin.Secp256k1` does not support older netstandard version.
///   * This will be obsolete when we drop the support for `netstandard2.1`
type ISecp256k1 =
    inherit IDisposable

    /// Create uncompressed public key(64 bytes) from private key (32 bytes)
    abstract member PublicKeyCreate:
        privateKeyInput: ReadOnlySpan<byte> -> bool * array<byte>

    /// Convert secp256k1 compatible style pubkey (64 bytes) into compressed form (33 bytes)
    abstract member PublicKeySerializeCompressed:
        publicKey: ReadOnlySpan<byte> -> bool * array<byte>

    /// Convert compressed pubkey (33 bytes) to secp256k1 compatible style (64 bytes).
    abstract member PublicKeyParse:
        serializedPublicKey: ReadOnlySpan<byte> -> bool * array<byte>

    /// Combine 2 public keys. Input can be either 33 bytes or 64 bytes. So normalization by PublicKeyParse is required.
    abstract member PublicKeyCombine:
        inputPubKey1: Span<byte> * inputPubKey2: Span<byte> ->
            bool * array<byte>

    /// Add a tweak (32 bytes) to a private key. Causes a mutation to `privateKeyToMutate`.
    abstract member PrivateKeyTweakAdd:
        tweak: ReadOnlySpan<byte> * privateKeyToMutate: Span<byte> -> bool

    /// Assume tweak (32 bytes) as a scalar and add `G` (basepoint) for tweak times. Causes a mutation to `privateKeyToMutate`
    abstract member PrivateKeyTweakMultiply:
        tweak: ReadOnlySpan<byte> * privKeyToMutate: Span<byte> -> bool

    /// Add a public key (64 bytes) to itself for tweak times. Causes a mutation to `pubKeyToMutate`
    abstract member PublicKeyTweakMultiply:
        tweak: ReadOnlySpan<byte> * pubKeyToMutate: Span<byte> -> bool

type ICryptoImpl =
    abstract member decryptWithAD:
        nonce: uint64 *
        key: uint256 *
        ad: array<byte> *
        cipherText: ReadOnlySpan<byte> ->
            Result<array<byte>, CryptoError>

    abstract member encryptWithAD:
        nonce: uint64 *
        key: uint256 *
        ad: ReadOnlySpan<byte> *
        plainText: ReadOnlySpan<byte> ->
            array<byte>

    /// This is used for filler generation in onion routing (BOLT 4)
    abstract member encryptWithoutAD:
        nonce: uint64 * key: array<byte> * plainText: ReadOnlySpan<byte> ->
            array<byte>

    abstract member newSecp256k1: unit -> ISecp256k1

#if !BouncyCastle
module Sodium =

    type NBitcoinSecp256k1() =
        let context = NBitcoin.Secp256k1.Context()

        member this.PublicKeyParse serializedPublicKey =
            match
                context.TryCreatePubKey
                    (
                        serializedPublicKey,
                        compressed = ref false
                    )
                with
            | true, pk ->
                let pk64 = Array.zeroCreate 65

                pk.WriteToSpan(compressed = false, output = pk64.AsSpan())
                |> ignore

                (true, pk64.[1..])
            | false, _ -> false, [||]

        /// Normalize any representation of PublicKey into secp256k1 internal representation. (64 bytes)
        member private this.NormalizePubKey(pk: ReadOnlySpan<byte>) =
            if pk.Length = 64 then
                pk
            else if pk.Length = 65 then
                pk.Slice(1)
            else if pk.Length = 33 then
                match this.PublicKeyParse(pk) with
                | false, _ ->
                    let hex = pk.ToArray().ToHexString()

                    raise
                    <| ArgumentException(
                        sprintf "Failed to parse public key %s" hex
                    )

                    ReadOnlySpan.Empty // to avoid weird compiler error
                | true, pk64 -> ReadOnlySpan(pk64)
            else
                raise
                <| ArgumentException(
                    sprintf "invalid public key with length %i" pk.Length
                )

                ReadOnlySpan.Empty // to avoid weird compiler error

        member private this.NormalizePubKey(pk: ECPubKey) =
            this.NormalizePubKey(ReadOnlySpan(pk.ToBytes()))

        interface ISecp256k1 with
            member this.PublicKeyCreate privKey =
                match context.TryCreateECPrivKey(privKey) with
                | true, priv ->
                    true,
                    this
                        .NormalizePubKey(priv.CreatePubKey())
                        .ToArray()
                | false, _ -> false, [||]

            member this.PublicKeySerializeCompressed pubKey =
                let pk = this.NormalizePubKey pubKey

                match
                    NBitcoin.Secp256k1.ECPubKey.TryCreateRawFormat
                        (
                            pk,
                            context
                        )
                    with
                | true, pk -> (true, pk.ToBytes(true))
                | false, _ -> false, [||]

            member this.PublicKeyParse serializedPublicKey =
                this.PublicKeyParse serializedPublicKey

            member this.PublicKeyCombine(pk1, pk2) =
                let pk1 = this.NormalizePubKey(Span<byte>.op_Implicit (pk1))
                let pk2 = this.NormalizePubKey(Span<byte>.op_Implicit (pk2))

                match
                    ECPubKey.TryCreateRawFormat(pk1, context),
                    ECPubKey.TryCreateRawFormat(pk2, context)
                    with
                | (true, pk1), (true, pk2) ->
                    match
                        NBitcoin.Secp256k1.ECPubKey.TryCombine
                            (
                                context,
                                seq {
                                    yield pk1
                                    yield pk2
                                }
                            )
                        with
                    | true, pk -> true, this.NormalizePubKey(pk).ToArray()
                    | false, _ -> false, [||]
                | _ ->
                    failwithf
                        "failed to combine public key %s and %s"
                        (pk1.ToArray().ToHexString())
                        (pk2.ToArray().ToHexString())

            member this.PrivateKeyTweakAdd(tweak, privateKey) =
                use ecPrivateKey =
                    context.CreateECPrivKey(Span<byte>.op_Implicit (privateKey))

                match ecPrivateKey.TryTweakAdd tweak with
                | true, r ->
                    r.WriteToSpan privateKey
                    true
                | false, _ -> false

            member this.PrivateKeyTweakMultiply(tweak, privateKey) =
                use ecPrivateKey =
                    context.CreateECPrivKey(Span<byte>.op_Implicit (privateKey))

                match ecPrivateKey.TryTweakMul tweak with
                | true, r ->
                    r.WriteToSpan privateKey
                    true
                | false, _ -> false

            member this.PublicKeyTweakMultiply(tweak, publicKey) =
                let pk: ReadOnlySpan<byte> = Span<byte>.op_Implicit (publicKey)
                let pk = this.NormalizePubKey pk

                match ECPubKey.TryCreateRawFormat(pk, context) with
                | true, ecPubKey ->
                    /// This function must update publicKey object which is 64 bytes.
                    /// But NBitcoin.Secp256k1 does not have a way to do that directly.
                    /// So We must first convert into uncompressed serialized form (65 bytes)
                    /// And normalize that by removing header byte.
                    let tweaked = ecPubKey.MultTweak tweak

                    let tweaked = this.NormalizePubKey(tweaked)
                    tweaked.CopyTo publicKey
                    true
                | false, _ -> false

            member this.Dispose() =
                ()

    let internal getNonce(n: uint64) =
        let nonceBytes =
            ReadOnlySpan(
                Array.concat
                    [|
                        Array.zeroCreate 4
                        BitConverter.GetBytes n
                    |]
            ) // little endian

        NSec.Cryptography.Nonce(nonceBytes, 0)

    let internal chacha20AD =
        NSec.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305

    let internal chacha20 = NSec.Experimental.ChaCha20.ChaCha20

    type CryptoImpl() =
        interface ICryptoImpl with
            member this.newSecp256k1() =
                new NBitcoinSecp256k1() :> ISecp256k1

            member this.decryptWithAD
                (
                    n: uint64,
                    key: uint256,
                    ad: array<byte>,
                    cipherText: ReadOnlySpan<byte>
                ) : Result<array<byte>, CryptoError> =
                let nonce = getNonce n
                let keySpan = ReadOnlySpan(key.ToBytes())
                let adSpan = ReadOnlySpan ad
                let blobF = NSec.Cryptography.KeyBlobFormat.RawSymmetricKey

                let chachaKey =
                    NSec.Cryptography.Key.Import(chacha20AD, keySpan, blobF)

                match chacha20AD.Decrypt(chachaKey, &nonce, adSpan, cipherText)
                    with
                | true, plainText -> Ok plainText
                | false, _ -> Error(BadMac)

            member this.encryptWithoutAD
                (
                    n: uint64,
                    key: array<byte>,
                    plainText: ReadOnlySpan<byte>
                ) =
                let nonce = getNonce n
                let keySpan = ReadOnlySpan key
                let blobF = NSec.Cryptography.KeyBlobFormat.RawSymmetricKey

                use chachaKey =
                    NSec.Cryptography.Key.Import(chacha20, keySpan, blobF)

                let res = chacha20.XOr(chachaKey, &nonce, plainText)
                res

            member this.encryptWithAD
                (
                    n: uint64,
                    key: uint256,
                    ad: ReadOnlySpan<byte>,
                    plainText: ReadOnlySpan<byte>
                ) =
                let nonce = getNonce n
                let keySpan = ReadOnlySpan(key.ToBytes())
                let blobF = NSec.Cryptography.KeyBlobFormat.RawSymmetricKey

                use chachaKey =
                    NSec.Cryptography.Key.Import(chacha20AD, keySpan, blobF)

                chacha20AD.Encrypt(chachaKey, &nonce, ad, plainText)

#else
type internal Operation =
    | Mul
    | Add

type internal BouncySecp256k1() =
    let parameters: Org.BouncyCastle.Asn1.X9.X9ECParameters =
        Org.BouncyCastle.Asn1.Sec.SecNamedCurves.GetByName "secp256k1"

    let ecParams =
        ECDomainParameters(
            parameters.Curve,
            parameters.G,
            parameters.N,
            parameters.H
        )

    let bcBigint(x: array<byte>) =
        Org.BouncyCastle.Math.BigInteger(1, x)

    let tweakKey
        (op: Operation)
        (tweak: ReadOnlySpan<byte>)
        (keyToMutate: Span<byte>)
        =
        let k = bcBigint <| keyToMutate.ToArray()
        let tweakInt = bcBigint <| tweak.ToArray()

        let tweaked =
            match op with
            | Mul -> k.Multiply tweakInt
            | Add -> k.Add tweakInt

        let tweakedByteArray = tweaked.Mod(parameters.N).ToByteArrayUnsigned()
        let offset = 32 - tweakedByteArray.Length

        tweakedByteArray
            .AsSpan()
            .CopyTo(keyToMutate.Slice offset)

        keyToMutate.Slice(0, offset).Fill 0uy
        true

    interface IDisposable with
        member this.Dispose() =
            ()

    interface ISecp256k1 with
        member this.PublicKeyCreate privKey =
            let privInt = bcBigint <| privKey.ToArray()
            true, ecParams.G.Multiply(privInt).GetEncoded true

        member this.PublicKeySerializeCompressed publicKey =
            let p = parameters.Curve.DecodePoint <| publicKey.ToArray()
            true, p.GetEncoded true

        member this.PublicKeyParse serializedPubKey =
            let p = parameters.Curve.DecodePoint <| serializedPubKey.ToArray()
            true, p.GetEncoded true

        member this.PublicKeyCombine(pubkey1, pubkey2) =
            let p1 = parameters.Curve.DecodePoint <| pubkey1.ToArray()
            let p2 = parameters.Curve.DecodePoint <| pubkey2.ToArray()
            true, p1.Add(p2).Normalize().GetEncoded true

        member this.PrivateKeyTweakAdd(tweak, privKeyToMutate) =
            tweakKey Add tweak privKeyToMutate

        member this.PrivateKeyTweakMultiply(tweak, privKeyToMutate) =
            tweakKey Mul tweak privKeyToMutate

        member this.PublicKeyTweakMultiply(tweak, publicKeyToMutate) =
            let p = parameters.Curve.DecodePoint <| publicKeyToMutate.ToArray()
            let tweakInt = bcBigint <| tweak.ToArray()
            let tweaked = p.Multiply tweakInt

            tweaked
                .Normalize()
                .GetEncoded(true)
                .AsSpan()
                .CopyTo publicKeyToMutate

            true

module BouncyCastle =
    type internal Mode =
        | Encrypt
        | Decrypt

    let internal encryptOrDecrypt
        (mode: Mode)
        (inp: array<byte>)
        (key: array<byte>)
        (nonce: array<byte>)
        (skip1block: bool)
        : array<byte> =
        let eng = Org.BouncyCastle.Crypto.Engines.ChaCha7539Engine()
        eng.Init((mode = Encrypt), ParametersWithIV(KeyParameter key, nonce))
        let out = Array.zeroCreate inp.Length

        if skip1block then
            let dummy = Array.zeroCreate 64
            eng.ProcessBytes(Array.zeroCreate 64, 0, 64, dummy, 0)

        eng.ProcessBytes(inp, 0, inp.Length, out, 0)
        out

    let internal pad (mac: Poly1305) (length: int) : unit =
        match length % 16 with
        | 0 -> ()
        | n ->
            let padding = Array.zeroCreate <| 16 - n
            mac.BlockUpdate(padding, 0, padding.Length)

    let internal writeLE (mac: Poly1305) (length: int) : unit =
        let serialized = BitConverter.GetBytes(uint64 length)

        if not BitConverter.IsLittleEndian then
            Array.Reverse serialized

        mac.BlockUpdate(serialized, 0, 8)

    let internal writeSpan (mac: Poly1305) (span: ReadOnlySpan<byte>) : unit =
        let byteArray = span.ToArray()
        mac.BlockUpdate(byteArray, 0, byteArray.Length)

    let internal calcMac key nonce ciphertext ad : array<byte> =
        let mac = Poly1305()

        let polyKey =
            encryptOrDecrypt Encrypt (Array.zeroCreate 32) key nonce false

        mac.Init <| KeyParameter polyKey
        writeSpan mac ad
        pad mac ad.Length
        mac.BlockUpdate(ciphertext, 0, ciphertext.Length)
        pad mac ciphertext.Length
        writeLE mac ad.Length
        writeLE mac ciphertext.Length
        let tag: array<byte> = Array.zeroCreate 16
        let macreslen = mac.DoFinal(tag, 0)
        assert (macreslen = 16)
        tag

    type CryptoImpl() =
        interface ICryptoImpl with
            member this.newSecp256k1() =
                new BouncySecp256k1() :> ISecp256k1

            member this.encryptWithAD
                (
                    n: uint64,
                    key: uint256,
                    ad: ReadOnlySpan<byte>,
                    plainText: ReadOnlySpan<byte>
                ) =
                let key = key.ToBytes()

                let nonce =
                    Array.concat
                        [|
                            Array.zeroCreate 4
                            BitConverter.GetBytes n
                        |]

                let plainTextBytes = plainText.ToArray()

                let ciphertext =
                    encryptOrDecrypt Encrypt plainTextBytes key nonce true

                let tag = calcMac key nonce ciphertext ad
                Array.concat [| ciphertext; tag |]

            member this.decryptWithAD
                (
                    n: uint64,
                    key: uint256,
                    ad: array<byte>,
                    ciphertext: ReadOnlySpan<byte>
                ) =
                if ciphertext.Length < 16 then
                    CryptoError.InvalidMessageLength ciphertext.Length |> Error
                else
                    let key = key.ToBytes()

                    let nonce =
                        Array.concat
                            [|
                                Array.zeroCreate 4
                                BitConverter.GetBytes n
                            |]

                    let ciphertextWithoutMac =
                        ciphertext
                            .Slice(0, ciphertext.Length - 16)
                            .ToArray()

                    let macToValidate =
                        ciphertext.Slice(ciphertext.Length - 16).ToArray()

                    let correctMac =
                        calcMac key nonce ciphertextWithoutMac (ReadOnlySpan ad)

                    if correctMac <> macToValidate then
                        Error(BadMac)
                    else
                        let plaintext =
                            encryptOrDecrypt
                                Decrypt
                                ciphertextWithoutMac
                                key
                                nonce
                                true

                        Ok plaintext

            member this.encryptWithoutAD
                (
                    n: uint64,
                    key: array<byte>,
                    plainText: ReadOnlySpan<byte>
                ) =
                let nonce =
                    Array.concat
                        [|
                            Array.zeroCreate 4
                            BitConverter.GetBytes n
                        |]

                encryptOrDecrypt Encrypt (plainText.ToArray()) key nonce false

#endif

module CryptoUtils =
#if BouncyCastle
    let impl = BouncyCastle.CryptoImpl() :> ICryptoImpl
#else
    let impl = Sodium.CryptoImpl() :> ICryptoImpl
#endif
