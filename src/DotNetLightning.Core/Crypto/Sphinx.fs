namespace DotNetLightning.Crypto

open System
open NBitcoin

open DotNetLightning.Utils
open DotNetLightning.Serialization
open DotNetLightning.Serialization.Msgs

open ResultUtils
open ResultUtils.Portability

/// Module to work with sphinx encryption.
/// Which is used in lightning network p2p onion routing.
/// see [bolt04](https://github.com/lightning/bolts/blob/master/04-onion-routing.md)
/// for more detail.
///
/// Usually you want to use high-level wrapper in `DotNetLightning.Peer`
/// for e.g. 3-way handshake and establishing the connection.
module Sphinx =
    open NBitcoin.Crypto

    let private crypto = CryptoUtils.impl

    [<Literal>]
    let VERSION = 0uy

    [<Literal>]
    let PayloadLength = 33

    [<Literal>]
    let HopDataSize = 1300

    [<Literal>]
    let MacLength = 32

    [<Literal>]
    let MaxHops = 20

    [<Literal>]
    let PACKET_LENGTH = 1366 // 1 + 33 + MacLength + MaxHops * (PayloadLength + MacLength)

    let private hex = NBitcoin.DataEncoders.HexEncoder()
    let private ascii = NBitcoin.DataEncoders.ASCIIEncoder()

    let private mac(key, msg) =
        Hashes.HMACSHA256(key, msg) |> uint256

    let private xor(a: array<byte>, b: array<byte>) =
        Array.zip a b |> Array.map(fun (abyte, bbyte) -> (abyte ^^^ bbyte))

    let private generateKey(key, secret) =
        let kb = key |> ascii.DecodeData
        Hashes.HMACSHA256(kb, secret)

    let private zeros l =
        Array.zeroCreate l

    let private generateStream(key, l) : array<byte> =
        crypto.encryptWithoutAD(0UL, key, ReadOnlySpan(Array.zeroCreate l))

    let private computeSharedSecret = Secret.FromKeyPair

    let private computeBlindingFactor (pk: PubKey) (secret: Key) =
        [| pk.ToBytes(); secret.ToBytes() |]
        |> Array.concat
        |> Crypto.Hashes.SHA256
        |> fun h -> new Key(h)

    let private blind (pk: PubKey) (secret: Key) =
        pk.GetSharedPubkey(secret)

    let private blindMulti (pk: PubKey) (secrets: seq<Key>) =
        Seq.fold (blind) pk secrets

    // computes ephemeral public keys and shared secretes for all nodes on the route
    let rec private computeEphemeralPublicKeysAndSharedSecretsCore
        (sessionKey: Key)
        (pubKeys: list<PubKey>)
        (ephemeralPubKeys: list<PubKey>)
        (blindingFactors: list<Key>)
        (sharedSecrets: list<Key>)
        =
        if (pubKeys.Length = 0) then
            (ephemeralPubKeys, sharedSecrets)
        else
            let ephemeralPubKey =
                blind
                    (ephemeralPubKeys |> List.last)
                    (blindingFactors |> List.last)

            let secret =
                computeSharedSecret(
                    blindMulti (pubKeys.[0]) (blindingFactors),
                    sessionKey
                )
                |> fun h -> new Key(h)

            let blindingFactor =
                computeBlindingFactor (ephemeralPubKey) (secret)

            computeEphemeralPublicKeysAndSharedSecretsCore
                sessionKey
                (pubKeys |> List.tail)
                (ephemeralPubKeys @ [ ephemeralPubKey ])
                (blindingFactors @ [ blindingFactor ])
                (sharedSecrets @ [ secret ])

    let rec internal computeEphemeralPublicKeysAndSharedSecrets
        (sessionKey: Key)
        (pubKeys: list<PubKey>)
        =
        let ephemeralPK0 = sessionKey.PubKey

        let secret0 =
            computeSharedSecret(pubKeys.[0], sessionKey) |> fun h -> new Key(h)

        let blindingFactor0 = computeBlindingFactor (ephemeralPK0) (secret0)

        computeEphemeralPublicKeysAndSharedSecretsCore
            (sessionKey)
            (pubKeys |> List.tail)
            ([ ephemeralPK0 ])
            ([ blindingFactor0 ])
            ([ secret0 ])

    let rec internal generateFiller
        (keyType: string)
        (payloads: list<array<byte>>)
        (sharedSecrets: list<Key>)
        =
        let fillerSize =
            payloads.[1..]
            |> List.sumBy(fun payload -> payload.Length + MacLength)

        let rec fillInner (filler: array<byte>) (i: int) : array<byte> =
            if i = payloads.Length - 1 then
                filler
            else
                let fillerOffset =
                    payloads.[.. i - 1]
                    |> List.sumBy(fun payload -> payload.Length + MacLength)

                let fillerStart = HopDataSize - fillerOffset
                let fillerEnd = HopDataSize + payloads.[i].Length + MacLength
                let fillerLength = fillerEnd - fillerStart

                let key = generateKey(keyType, sharedSecrets.[i].ToBytes())

                let stream =
                    let s = generateStream(key, fillerEnd)
                    s.[fillerStart .. fillerEnd - 1]

                let newFiller =
                    [
                        xor(Array.take fillerLength filler, stream)
                        Array.skip fillerLength filler
                    ]
                    |> Array.concat

                fillInner newFiller (i + 1)

        fillInner (Array.zeroCreate fillerSize) 0

    type ParsedPacket =
        {
            Payload: array<byte>
            NextPacket: OnionPacket
            SharedSecret: array<byte>
        }

    let parsePacket
        (nodePrivateKey: Key)
        (ad: array<byte>)
        (rawPacket: array<byte>)
        : Result<ParsedPacket, CryptoError> =
        if (rawPacket.Length <> PACKET_LENGTH) then
            CryptoError.InvalidErrorPacketLength(
                PACKET_LENGTH,
                rawPacket.Length
            )
            |> Error
        else
            let packet =
                ILightningSerializable.fromBytes<OnionPacket>(rawPacket)

            match PubKey.TryCreatePubKey packet.PublicKey with
            | false, _ -> InvalidPublicKey(packet.PublicKey) |> Error
            | true, publicKey ->
                let ss = computeSharedSecret(publicKey, nodePrivateKey)
                let mu = generateKey("mu", ss)

                let check =
                    let msg = Array.concat(seq [ packet.HopData; ad ])
                    mac(mu, msg)

                if check <> packet.HMAC then
                    CryptoError.BadMac |> Error
                else
                    let rho = generateKey("rho", ss)

                    let bin =
                        let d =
                            Array.concat(
                                seq
                                    [
                                        packet.HopData
                                        zeros(PayloadLength + MacLength)
                                    ]
                            )

                        let dataLength =
                            PayloadLength
                            + MacLength
                            + MaxHops * (PayloadLength + MacLength)

                        xor(d, generateStream(rho, dataLength))

                    let payload = bin.[0 .. PayloadLength - 1]

                    let hmac =
                        bin.[PayloadLength .. PayloadLength + MacLength - 1]
                        |> uint256

                    let nextRouteInfo = bin.[PayloadLength + MacLength ..]

                    let nextPubKey =
                        use sharedSecret = new Key(ss)

                        blind
                            publicKey
                            (computeBlindingFactor publicKey sharedSecret)

                    {
                        ParsedPacket.Payload = payload
                        NextPacket =
                            {
                                Version = VERSION
                                PublicKey = nextPubKey.ToBytes()
                                HMAC = hmac
                                HopData = nextRouteInfo
                            }
                        SharedSecret = ss
                    }
                    |> Ok

    /// Compute the next packet from the current packet and node parameters.
    /// Packets are constructed in reverse order:
    /// - you first build the last packet
    /// - then you call makeNextPacket(...) until you've build the final onion packet
    ///   that will be sent to the first node
    let internal makeNextPacket
        (
            payload: array<byte>,
            ad: array<byte>,
            ephemeralPubKey: PubKey,
            sharedSecret: array<byte>,
            packet: OnionPacket,
            routingInfoFiller: option<array<byte>>
        ) =
        let payloadLen = payload.Length
        let filler = defaultArg routingInfoFiller ([||])

        let nextRoutingInfo =
            let routingInfo1 =
                seq
                    [
                        payload
                        packet.HMAC.ToBytes()
                        (packet.HopData
                         |> Array.skipBack(payloadLen + MacLength))
                    ]
                |> Array.concat

            let routingInfo2 =
                let rho = generateKey("rho", sharedSecret)
                let numHops = MaxHops * (PayloadLength + MacLength)
                xor(routingInfo1, generateStream(rho, numHops))

            Array.append (routingInfo2 |> Array.skipBack filler.Length) filler

        let nextHmac =
            let macKey = generateKey("mu", sharedSecret)
            let macMsg = (Array.append nextRoutingInfo ad)
            mac(macKey, macMsg)

        let nextPacket =
            {
                OnionPacket.Version = VERSION
                PublicKey = ephemeralPubKey.ToBytes()
                HopData = nextRoutingInfo
                HMAC = nextHmac
            }

        nextPacket

    module PacketFiller =
        // DeterministicPacketFiller is a packet filler that generates a deterministic
        // set of filler bytes by using chacha20 with a key derived from the session
        // key.
        let DeterministicPacketFiller(sessionKey: Key) =
            generateStream(
                generateKey("pad", sessionKey.ToBytes()),
                HopDataSize
            )

        // BlankPacketFiller is a packet filler that doesn't attempt to fill out the
        // packet at all. It should ONLY be used for generating test vectors or other
        // instances that required deterministic packet generation.
        [<Obsolete("BlankPacketFiller is obsolete, see here: https://github.com/lightningnetwork/lightning-rfc/commit/8dd0b75809c9a7498bb9031a6674e5f58db509f4",
                   false)>]
        let BlankPacketFiller _ =
            Array.zeroCreate HopDataSize

    type PacketAndSecrets =
        {
            Packet: OnionPacket
            /// Shared secrets (one per node in the route). Known (and needed) only if you're creating the
            /// packet. Empty if you're just forwarding the packet to the next node
            SharedSecrets: list<(Key * PubKey)>
        }

        static member Create
            (
                sessionKey: Key,
                pubKeys: list<PubKey>,
                payloads: list<array<byte>>,
                ad: array<byte>,
                initialPacketFiller: Key -> array<byte>
            ) =
            let (ephemeralPubKeys, sharedSecrets) =
                computeEphemeralPublicKeysAndSharedSecrets
                    (sessionKey)
                    (pubKeys)

            let filler = generateFiller "rho" payloads sharedSecrets

            let initialPacket =
                { OnionPacket.LastPacket with
                    HopData = initialPacketFiller sessionKey
                }

            let lastPacket =
                makeNextPacket(
                    payloads |> List.last,
                    ad,
                    ephemeralPubKeys |> List.last,
                    (sharedSecrets |> List.last |> (fun ss -> ss.ToBytes())),
                    initialPacket,
                    Some(filler)
                )

            let rec loop
                (
                    hopPayloads: list<array<byte>>,
                    ephKeys: list<PubKey>,
                    ss: list<Key>,
                    packet: OnionPacket
                ) =
                if hopPayloads.IsEmpty then
                    packet
                else
                    let nextPacket =
                        makeNextPacket(
                            hopPayloads |> List.last,
                            ad,
                            ephKeys |> List.last,
                            (ss |> List.last |> (fun (s: Key) -> s.ToBytes())),
                            packet,
                            None
                        )

                    loop(
                        hopPayloads.[0 .. hopPayloads.Length - 2],
                        ephKeys.[0 .. ephKeys.Length - 2],
                        ss.[0 .. ss.Length - 2],
                        nextPacket
                    )

            let p =
                loop(
                    payloads.[0 .. payloads.Length - 2],
                    ephemeralPubKeys.[0 .. ephemeralPubKeys.Length - 2],
                    sharedSecrets.[0 .. sharedSecrets.Length - 2],
                    lastPacket
                )

            {
                PacketAndSecrets.Packet = p
                SharedSecrets = List.zip sharedSecrets pubKeys
            }

    [<Literal>]
    let MAX_ERROR_PAYLOAD_LENGTH = 256

    [<Literal>]
    let ERROR_PACKET_LENGTH = 292 // MacLength + MAX_ERROR_PAYLOAD_LENGTH + 2 + 2

    let forwardErrorPacket(packet: array<byte>, ss: array<byte>) =
        assert (packet.Length = ERROR_PACKET_LENGTH)
        let k = generateKey("ammag", ss)
        let s = generateStream(k, ERROR_PACKET_LENGTH)
        xor(packet, s)

    let private checkMac(ss: array<byte>, packet: array<byte>) : bool =
        let (macV, payload) = packet |> Array.splitAt(MacLength)
        let um = generateKey("um", ss)
        (macV |> uint256) = mac(um, payload)

    let private extractFailureMessage(packet: array<byte>) =
        if (packet.Length <> ERROR_PACKET_LENGTH) then
            InvalidErrorPacketLength(ERROR_PACKET_LENGTH, packet.Length)
            |> Error
        else
            let (_mac, payload) = packet |> Array.splitAt(MacLength)
            let len = Utils.ToUInt16(payload.[0..1], false) |> int

            if (len < 0 || (len > MAX_ERROR_PAYLOAD_LENGTH)) then
                InvalidMessageLength len |> Error
            else
                let msg = payload.[2 .. 2 + len - 1]
                ILightningSerializable.fromBytes<FailureMsg>(msg) |> Ok

    type ErrorPacket =
        {
            OriginNode: NodeId
            FailureMsg: FailureMsg
        }

        static member Create(ss: array<byte>, msg: FailureMsg) =
            let msgB = msg.ToBytes()
            assert (msgB.Length <= MAX_ERROR_PAYLOAD_LENGTH)
            let um = generateKey("um", ss)
            let padLen = MAX_ERROR_PAYLOAD_LENGTH - msgB.Length

            let payload =
                use ms = new System.IO.MemoryStream()
                use st = new LightningWriterStream(ms)
                st.Write(uint16 msgB.Length, false)
                st.Write(msgB)
                st.Write(uint16 padLen, false)
                st.Write(zeros padLen)
                ms.ToArray()

            forwardErrorPacket(
                Array.append (mac(um, payload).ToBytes()) payload,
                ss
            )

        static member TryParse(packet: array<byte>, ss: list<(Key * PubKey)>) =
            let ssB = ss |> List.map(fun (k, pk) -> (k.ToBytes(), pk))
            ErrorPacket.TryParse(packet, ssB)

        static member TryParse
            (
                packet: array<byte>,
                ss: list<(array<byte> * PubKey)>
            ) : Result<ErrorPacket, CryptoError> =
            if (packet.Length <> ERROR_PACKET_LENGTH) then
                InvalidErrorPacketLength(ERROR_PACKET_LENGTH, packet.Length)
                |> Error
            else
                let rec loop
                    (
                        packet: array<byte>,
                        ss: list<(array<byte> * PubKey)>
                    ) =
                    match ss with
                    | [] -> FailedToParseErrorPacket(packet, ss) |> Error
                    | (secret, pk) :: tail ->
                        let packet1 = forwardErrorPacket(packet, secret)

                        if ((checkMac(secret, packet1))) then
                            extractFailureMessage packet1
                            >>= fun msg ->
                                    {
                                        OriginNode = pk |> NodeId
                                        FailureMsg = msg
                                    }
                                    |> Ok
                        else
                            loop(packet1, tail)

                loop(packet, ss)
