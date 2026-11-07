package com.yongshuai.paxvm

import android.content.Context
import android.os.Build
import android.util.Base64
import org.bouncycastle.crypto.digests.SHA256Digest
import org.bouncycastle.crypto.generators.HKDFBytesGenerator
import org.bouncycastle.crypto.params.HKDFParameters
import java.io.ByteArrayOutputStream
import java.io.EOFException
import java.io.File
import java.io.IOException
import java.io.InputStream
import java.io.OutputStream
import java.math.BigInteger
import java.net.InetSocketAddress
import java.net.Socket
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.security.KeyFactory
import java.security.KeyPair
import java.security.KeyPairGenerator
import java.security.MessageDigest
import java.security.PrivateKey
import java.security.SecureRandom
import java.security.Signature
import java.security.cert.CertificateFactory
import java.security.cert.X509Certificate
import java.security.interfaces.RSAPrivateCrtKey
import java.security.interfaces.RSAPublicKey
import java.security.spec.PKCS8EncodedKeySpec
import java.security.spec.RSAPublicKeySpec
import java.util.Locale
import javax.crypto.Cipher
import javax.crypto.spec.GCMParameterSpec
import javax.crypto.spec.SecretKeySpec
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLException
import javax.net.ssl.SSLSocket
import javax.net.ssl.X509KeyManager
import javax.net.ssl.X509TrustManager

/**
 * Minimal local ADB client: talks to the device's own wireless
 * debugging adbd on 127.0.0.1 (pairing port + connect port) so
 * the shell can run device-owner-level shell commands (settings /
 * device_config) without root or a PC.
 *
 * Written from the protocol references, not copied:
 * - Wire format + auth: AOSP adb protocol.txt, cross-checked
 *   against libadb-android (AdbProtocol / AdbConnection /
 *   AdbStream / PairingConnectionCtx / PairingAuthCtx /
 *   AndroidPubkey) by MuntashirAkon.
 * - SPAKE2: implemented directly from BoringSSL's
 *   spake25519.c (SPAKE2_generate_msg / SPAKE2_process_msg),
 *   because the spake2-java port libadb depends on fails its own
 *   key-agreement tests (verified locally: its Spake25519Test
 *   spake2/oldAlice/oldBob cases fail). The group arithmetic here
 *   was validated byte-for-byte against an independent Python
 *   model using the BoringSSL test inputs (same password and
 *   ephemeral keys -> same messages and session key).
 */

// ADB wire constants (AOSP protocol.txt; libadb AdbProtocol.java).
internal object AdbProtocol {
    const val A_SYNC = 0x434e5953
    const val A_CNXN = 0x4e584e43
    const val A_AUTH = 0x48545541
    const val A_OPEN = 0x4e45504f
    const val A_OKAY = 0x59414b4f
    const val A_CLSE = 0x45534c43
    const val A_WRTE = 0x45545257
    const val A_STLS = 0x534c5453

    // A_STLS arg0 value announcing TLS support (libadb AdbProtocol).
    const val A_STLS_VERSION = 0x01000000
    const val A_VERSION_MIN = 0x01000000

    // Skips the payload checksum verification on the peer side.
    const val A_VERSION_SKIP_CHECKSUM = 0x01000001
    const val MAX_PAYLOAD_V2 = 256 * 1024
    const val MAX_PAYLOAD_V3 = 1024 * 1024

    const val AUTH_TOKEN = 1
    const val AUTH_SIGNATURE = 2
    const val AUTH_RSAPUBLICKEY = 3
    const val HEADER_SIZE = 24

    fun versionForSdk(): Int =
        if (Build.VERSION.SDK_INT >= 28) A_VERSION_SKIP_CHECKSUM else A_VERSION_MIN

    fun maxDataForSdk(): Int =
        if (Build.VERSION.SDK_INT >= 28) MAX_PAYLOAD_V3 else MAX_PAYLOAD_V2
}

internal class AdbMessage(
    val command: Int,
    val arg0: Int,
    val arg1: Int,
    val payload: ByteArray,
) {
    fun commandName(): String = when (command) {
        AdbProtocol.A_SYNC -> "SYNC"
        AdbProtocol.A_CNXN -> "CNXN"
        AdbProtocol.A_AUTH -> "AUTH"
        AdbProtocol.A_OPEN -> "OPEN"
        AdbProtocol.A_OKAY -> "OKAY"
        AdbProtocol.A_CLSE -> "CLSE"
        AdbProtocol.A_WRTE -> "WRTE"
        AdbProtocol.A_STLS -> "STLS"
        else -> "0x%08x".format(command)
    }
}

@Throws(IOException::class)
internal fun writeAdbMessage(
    out: OutputStream,
    command: Int,
    arg0: Int,
    arg1: Int,
    payload: ByteArray?,
) {
    val data = payload ?: ByteArray(0)
    // Checksum is always computed on send (libadb does the same);
    // peers on A_VERSION_SKIP_CHECKSUM simply ignore it.
    var check = 0
    for (b in data) check += b.toInt() and 0xFF
    val hdr = ByteBuffer.allocate(AdbProtocol.HEADER_SIZE).order(ByteOrder.LITTLE_ENDIAN)
    hdr.putInt(command)
    hdr.putInt(arg0)
    hdr.putInt(arg1)
    hdr.putInt(data.size)
    hdr.putInt(check)
    hdr.putInt(command.inv())
    out.write(hdr.array())
    if (data.isNotEmpty()) out.write(data)
    out.flush()
}

@Throws(IOException::class)
internal fun readFully(inp: InputStream, n: Int): ByteArray {
    val buf = ByteArray(n)
    var off = 0
    while (off < n) {
        val r = inp.read(buf, off, n - off)
        if (r < 0) throw EOFException("stream closed after $off of $n bytes")
        off += r
    }
    return buf
}

@Throws(IOException::class)
internal fun readAdbMessage(inp: InputStream): AdbMessage {
    val hdr = readFully(inp, AdbProtocol.HEADER_SIZE)
    val bb = ByteBuffer.wrap(hdr).order(ByteOrder.LITTLE_ENDIAN)
    val command = bb.int
    val arg0 = bb.int
    val arg1 = bb.int
    val len = bb.int
    bb.int // data_check, not verified (matches libadb behaviour)
    val magic = bb.int
    if (magic != command.inv()) {
        throw IOException("ADB header magic mismatch for command 0x%08x".format(command))
    }
    if (len < 0 || len > AdbProtocol.MAX_PAYLOAD_V3) {
        throw IOException("ADB payload length out of range: $len")
    }
    val payload = if (len == 0) ByteArray(0) else readFully(inp, len)
    return AdbMessage(command, arg0, arg1, payload)
}

/**
 * The app's persistent ADB identity: one RSA-2048 key pair plus a
 * self-signed certificate carrying it. Stored as PKCS#8 + DER in
 * filesDir (adb_key.pk8 / adb_cert.der), created on first use and
 * reused afterwards; adbd remembers the public half at pairing
 * time and later authenticates us by the TLS client certificate.
 */
class AdbKeys(context: Context) {
    val privateKey: PrivateKey
    val publicKey: RSAPublicKey
    val certificate: X509Certificate

    init {
        val keyFile = File(context.filesDir, KEY_FILE)
        val certFile = File(context.filesDir, CERT_FILE)
        var loaded: Triple<PrivateKey, RSAPublicKey, X509Certificate>? = null
        if (keyFile.isFile && certFile.isFile) {
            try {
                loaded = load(keyFile, certFile)
            } catch (e: Exception) {
                loaded = null // corrupt pair: fall through and mint a fresh one
            }
        }
        if (loaded != null) {
            privateKey = loaded.first
            publicKey = loaded.second
            certificate = loaded.third
        } else {
            val kp = KeyPairGenerator.getInstance("RSA").apply { initialize(2048) }
                .generateKeyPair()
            val certDer = DerCert.selfSign(kp, CERT_CN)
            val cert = parseCert(certDer)
            keyFile.writeBytes(kp.private.encoded) // PKCS#8
            certFile.writeBytes(certDer)
            privateKey = kp.private
            publicKey = kp.public as RSAPublicKey
            certificate = cert
        }
    }

    private fun load(
        keyFile: File,
        certFile: File,
    ): Triple<PrivateKey, RSAPublicKey, X509Certificate> {
        val kf = KeyFactory.getInstance("RSA")
        val priv = kf.generatePrivate(PKCS8EncodedKeySpec(keyFile.readBytes()))
        val crt = priv as? RSAPrivateCrtKey
            ?: throw IOException("stored ADB key is not an RSA CRT key")
        val pub = kf.generatePublic(
            RSAPublicKeySpec(crt.modulus, crt.publicExponent),
        ) as RSAPublicKey
        val cert = parseCert(certFile.readBytes())
        if (!cert.publicKey.encoded.contentEquals(pub.encoded)) {
            throw IOException("stored ADB certificate does not match stored key")
        }
        return Triple(priv, pub, cert)
    }

    private fun parseCert(der: ByteArray): X509Certificate =
        CertificateFactory.getInstance("X.509")
            .generateCertificate(der.inputStream()) as X509Certificate

    /**
     * AOSP RSAPublicKey blob (libcrypto_utils/android_pubkey.cpp):
     * 524 bytes little-endian: modulus_size_words(64), n0inv,
     * modulus (256B, little-endian words), rr = 2^4096 mod n
     * (256B), exponent. Word order inside each big value is
     * little-endian byte order of the integer.
     */
    fun androidPubkeyBlob(): ByteArray {
        val n = publicKey.modulus
        val r32 = BigInteger.ONE.shiftLeft(32)
        // n0inv = -(n[0])^-1 mod 2^32 (AOSP comment), computed as
        // 2^32 - (n mod 2^32)^-1 so the value stays unsigned.
        val n0inv = r32.subtract(n.mod(r32).modInverse(r32))
        val rr = BigInteger.ONE.shiftLeft(4096).mod(n)
        val out = ByteArrayOutputStream(ANDROID_PUBKEY_SIZE)
        writeU32Le(out, MODULUS_SIZE_WORDS.toLong())
        writeU32Le(out, n0inv.toLong())
        writeFixedLe(out, n, MODULUS_SIZE_BYTES)
        writeFixedLe(out, rr, MODULUS_SIZE_BYTES)
        writeU32Le(out, publicKey.publicExponent.toLong())
        return out.toByteArray()
    }

    /** Base64(blob) + " " + name + NUL (AndroidPubkey.encodeWithName). */
    fun encodeWithName(name: String): ByteArray {
        val b64 = Base64.encode(androidPubkeyBlob(), Base64.NO_WRAP)
        val suffix = " $name\u0000".toByteArray(Charsets.UTF_8)
        return b64 + suffix
    }

    /**
     * ADB AUTH signature (AOSP adb_auth_sign, via libadb
     * AndroidPubkey.adbAuthSign): RSA private operation over the
     * fixed PKCS#1 v1.5 block 00 01 FF..FF 00 || SHA-1 DigestInfo
     * prefix || 20-byte token, with RSA/ECB/NoPadding.
     */
    fun authSign(token: ByteArray): ByteArray {
        val block = ByteArray(MODULUS_SIZE_BYTES)
        block[0] = 0x00
        block[1] = 0x01
        val digestInfo = byteArrayOf(
            0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e,
            0x03, 0x02, 0x1a, 0x05, 0x00, 0x04, 0x14,
        )
        val ffEnd = block.size - 1 - digestInfo.size - token.size
        for (i in 2 until ffEnd) block[i] = 0xFF.toByte()
        block[ffEnd] = 0x00
        System.arraycopy(digestInfo, 0, block, ffEnd + 1, digestInfo.size)
        System.arraycopy(token, 0, block, ffEnd + 1 + digestInfo.size, token.size)
        val cipher = Cipher.getInstance("RSA/ECB/NoPadding")
        cipher.init(Cipher.ENCRYPT_MODE, privateKey)
        return cipher.doFinal(block)
    }

    private fun writeU32Le(out: ByteArrayOutputStream, v: Long) {
        out.write((v and 0xFF).toInt())
        out.write(((v shr 8) and 0xFF).toInt())
        out.write(((v shr 16) and 0xFF).toInt())
        out.write(((v shr 24) and 0xFF).toInt())
    }

    private fun writeFixedLe(out: ByteArrayOutputStream, v: BigInteger, len: Int) {
        val be = v.toByteArray()
        val buf = ByteArray(len)
        var i = 0
        while (i < minOf(len, be.size)) {
            buf[i] = be[be.size - 1 - i]
            i++
        }
        out.write(buf)
    }

    companion object {
        const val KEY_FILE = "adb_key.pk8"
        const val CERT_FILE = "adb_cert.der"
        const val CERT_CN = "PaxVM"
        const val ANDROID_PUBKEY_SIZE = 524
        const val MODULUS_SIZE_WORDS = 64
        const val MODULUS_SIZE_BYTES = 256
    }
}

/**
 * Hand-rolled DER self-signed X.509 v3 certificate for the ADB
 * key. adbd only compares the public key inside the TLS client
 * certificate with the key stored at pairing time; the desktop
 * adb identity certificate is equally plain. The usual shortcut
 * (com.sun.security.x509 internal APIs, used by libadb's test
 * app) is not available/stable on Android, so the TBSCertificate
 * is encoded directly: version [0]=2, random serial,
 * SHA256withRSAEncryption, issuer=subject=CN, validity,
 * subjectPublicKeyInfo taken verbatim from the generated key.
 */
internal object DerCert {
    private fun der(tag: Int, content: ByteArray): ByteArray {
        val out = ByteArrayOutputStream()
        out.write(tag)
        val len = content.size
        when {
            len < 128 -> out.write(len)
            len < 256 -> {
                out.write(0x81)
                out.write(len)
            }
            else -> {
                out.write(0x82)
                out.write((len shr 8) and 0xFF)
                out.write(len and 0xFF)
            }
        }
        out.write(content)
        return out.toByteArray()
    }

    private fun seq(vararg parts: ByteArray): ByteArray {
        val body = ByteArrayOutputStream()
        for (part in parts) body.write(part)
        return der(0x30, body.toByteArray())
    }

    private fun intDer(v: BigInteger): ByteArray = der(0x02, v.toByteArray())

    // OID 1.2.840.113549.1.1.11 (sha256WithRSAEncryption), DER body.
    private fun algId(): ByteArray = seq(
        der(0x06, byteArrayOf(0x2a, 0x86.toByte(), 0x48, 0x86.toByte(), 0xf7.toByte(), 0x0d, 0x01, 0x01, 0x0b)),
        byteArrayOf(0x05, 0x00), // NULL parameters
    )

    // Name with a single CN RDN (OID 2.5.4.3, UTF8String).
    private fun nameCn(cn: String): ByteArray {
        val atv = seq(
            der(0x06, byteArrayOf(0x55, 0x04, 0x03)),
            der(0x0c, cn.toByteArray(Charsets.UTF_8)),
        )
        return seq(der(0x31, atv))
    }

    private fun timeDer(epochMs: Long, generalized: Boolean): ByteArray {
        val pattern = if (generalized) "yyyyMMddHHmmss'Z'" else "yyMMddHHmmss'Z'"
        val fmt = java.text.SimpleDateFormat(pattern, Locale.US)
        fmt.timeZone = java.util.TimeZone.getTimeZone("UTC")
        val text = fmt.format(java.util.Date(epochMs))
        return der(if (generalized) 0x18 else 0x17, text.toByteArray(Charsets.US_ASCII))
    }

    /** Returns the DER encoding of a self-signed cert for [kp]. */
    fun selfSign(kp: KeyPair, cn: String): ByteArray {
        val now = System.currentTimeMillis()
        val twentyYearsMs = 20L * 365 * 24 * 3600 * 1000
        val alg = algId()
        val name = nameCn(cn)
        val validity = seq(
            timeDer(now - 24L * 3600 * 1000, generalized = false),
            timeDer(now + twentyYearsMs, generalized = true),
        )
        val serial = BigInteger(64, SecureRandom()).abs().add(BigInteger.ONE)
        val tbs = seq(
            der(0xa0, intDer(BigInteger.valueOf(2))), // [0] version: v3
            intDer(serial),
            alg,
            name, // issuer
            validity,
            name, // subject
            kp.public.encoded, // subjectPublicKeyInfo, already DER
        )
        val signer = Signature.getInstance("SHA256withRSA")
        signer.initSign(kp.private)
        signer.update(tbs)
        val sigBytes = signer.sign()
        val bitString = ByteArrayOutputStream()
        bitString.write(0) // unused-bits count
        bitString.write(sigBytes)
        return seq(tbs, alg, der(0x03, bitString.toByteArray()))
    }
}

/**
 * SPAKE2 over Edwards25519, Alice side, following BoringSSL
 * spake25519.c step for step:
 * - ephemeral scalar: sc_reduce(64 random bytes) << 3
 * - password scalar: sc_reduce(SHA-512(password)) plus the
 *   unilateral cofactor hack (add l / 2l / 4l while the low
 *   three bits demand it) from SPAKE2_generate_msg
 * - mask point: password_scalar * M (Alice) or * N (Bob), with
 *   M / N the decodings of SHA-256("edwards25519 point
 *   generation seed (M)" / "(N)")
 * - key: SHA-512 over length-prefixed (client name, server
 *   name, client msg, server msg, DH, password hash)
 * Point arithmetic is plain BigInteger affine Edwards math
 * (add-2008-hwcd formulas): variable-time, acceptable here —
 * the peer is the device's own adbd on loopback and the secret
 * is a 6-digit pairing code whose value expires with the
 * pairing dialog. Validated against an independent Python
 * implementation on the BoringSSL test vectors.
 */
internal class Spake2Core(private val alice: Boolean) {

    internal class Pt(val x: BigInteger, val y: BigInteger)

    private var priv: BigInteger? = null
    private var pwHash: ByteArray? = null
    private var pwScalar: BigInteger? = null
    private var myMsg: ByteArray? = null

    fun generateMessage(password: ByteArray, privRandom64: ByteArray): ByteArray {
        val p = scReduce(privRandom64).shiftLeft(3)
        priv = p
        val hash = MessageDigest.getInstance("SHA-512").digest(password)
        pwHash = hash
        // Password scalar with the BoringSSL copy-paste-omission
        // hack (see class doc): bits are tested on the running
        // value, exactly like the C code.
        var s = scReduce(hash)
        var order = L
        if (s.testBit(0)) s = s.add(order)
        order = order.shiftLeft(1)
        if (s.testBit(1)) s = s.add(order)
        order = order.shiftLeft(1)
        if (s.testBit(2)) s = s.add(order)
        pwScalar = s
        val base = mul(BASE, p)
        val mask = mul(if (alice) M_POINT else N_POINT, s)
        val msg = encodePt(add(base, mask))
        myMsg = msg
        return msg.copyOf()
    }

    fun processMessage(theirMsg: ByteArray): ByteArray {
        val my = myMsg ?: throw IllegalStateException("generateMessage not called")
        val scalar = pwScalar ?: throw IllegalStateException("generateMessage not called")
        val p = priv ?: throw IllegalStateException("generateMessage not called")
        val qStar = decodePt(theirMsg)
        val peerMask = mul(if (alice) N_POINT else M_POINT, scalar)
        val q = add(qStar, neg(peerMask))
        val dh = encodePt(mul(q, p))
        val sha = MessageDigest.getInstance("SHA-512")
        fun feed(part: ByteArray) {
            val len = ByteArray(8)
            var v = part.size.toLong()
            for (i in 0 until 8) {
                len[i] = (v and 0xFF).toByte()
                v = v shr 8
            }
            sha.update(len)
            sha.update(part)
        }
        // Transcript order is always (client, server), both roles.
        feed(CLIENT_NAME)
        feed(SERVER_NAME)
        feed(if (alice) my else theirMsg)
        feed(if (alice) theirMsg else my)
        feed(dh)
        feed(pwHash!!)
        return sha.digest()
    }

    companion object {
        // "adb pair client" / "adb pair server" with trailing NUL
        // (AOSP pairing_connection names, 16 bytes each).
        private val CLIENT_NAME = "adb pair client\u0000".toByteArray(Charsets.UTF_8)
        private val SERVER_NAME = "adb pair server\u0000".toByteArray(Charsets.UTF_8)

        private val P: BigInteger =
            BigInteger.ONE.shiftLeft(255).subtract(BigInteger.valueOf(19))
        private val D = BigInteger(
            "37095705934669439343138083508754565189542113879843219016388785533085940283555",
        )
        private val L: BigInteger = BigInteger.ONE.shiftLeft(252)
            .add(BigInteger("27742317777372353535851937790883648493"))
        private val SQRT_M1: BigInteger =
            BigInteger.valueOf(2).modPow(P.subtract(BigInteger.ONE).shiftRight(2), P)
        private val EXP_E: BigInteger = P.subtract(BigInteger.valueOf(5)).shiftRight(3)

        private val BASE: Pt = run {
            val by = BigInteger.valueOf(4)
                .multiply(BigInteger.valueOf(5).modInverse(P)).mod(P)
            decodePt(encFromY(by, false))
        }
        private val M_POINT: Pt = decodePt(
            hexBytes("5ada7e4bf6ddd9adb6626d32131c6b5c51a1e347a3478f53cfcf441b88eed12e"),
        )
        private val N_POINT: Pt = decodePt(
            hexBytes("10e3df0ae37d8e7a99b5fe74b44672103dbddcbd06af680d71329a11693bc778"),
        )

        private fun hexBytes(s: String): ByteArray {
            val out = ByteArray(s.length / 2)
            for (i in out.indices) {
                out[i] = s.substring(2 * i, 2 * i + 2).toInt(16).toByte()
            }
            return out
        }

        private fun leToBigInt(b: ByteArray): BigInteger {
            val be = ByteArray(b.size)
            for (i in b.indices) be[i] = b[b.size - 1 - i]
            return BigInteger(1, be)
        }

        private fun bigIntToLe32(v: BigInteger): ByteArray {
            val be = v.toByteArray()
            val out = ByteArray(32)
            var i = 0
            while (i < minOf(32, be.size)) {
                out[i] = be[be.size - 1 - i]
                i++
            }
            return out
        }

        private fun encFromY(y: BigInteger, xOdd: Boolean): ByteArray {
            val b = bigIntToLe32(y)
            if (xOdd) b[31] = (b[31].toInt() or 0x80).toByte()
            return b
        }

        private fun scReduce(b64: ByteArray): BigInteger = leToBigInt(b64).mod(L)

        // Standard compressed-point decode (p == 5 mod 8 root
        // finding, RFC 8032 style); matches BoringSSL
        // ge_frombytes_vartime semantics used by SPAKE2.
        private fun decodePt(s: ByteArray): Pt {
            require(s.size == 32) { "encoded point must be 32 bytes" }
            val xOdd = (s[31].toInt() and 0x80) != 0
            val yb = s.copyOf()
            yb[31] = (yb[31].toInt() and 0x7f).toByte()
            val y = leToBigInt(yb)
            val yy = y.multiply(y).mod(P)
            val u = yy.subtract(BigInteger.ONE).mod(P)
            val v = D.multiply(yy).add(BigInteger.ONE).mod(P)
            var x = u.multiply(v.pow(3)).mod(P)
                .multiply(u.multiply(v.pow(7)).mod(P).modPow(EXP_E, P)).mod(P)
            val vx2 = v.multiply(x).multiply(x).mod(P)
            when {
                vx2 == u -> Unit
                vx2 == u.negate().mod(P) -> x = x.multiply(SQRT_M1).mod(P)
                else -> throw IllegalArgumentException("point is not on the curve")
            }
            if (x.testBit(0) != xOdd) x = P.subtract(x)
            return Pt(x, y)
        }

        private fun encodePt(pt: Pt): ByteArray = encFromY(pt.y, pt.x.testBit(0))

        // Twisted Edwards addition for a = -1 (add-2008-hwcd).
        private fun add(a: Pt, b: Pt): Pt {
            val t = D.multiply(a.x).mod(P).multiply(b.x).mod(P)
                .multiply(a.y).mod(P).multiply(b.y).mod(P)
            val x = a.x.multiply(b.y).add(b.x.multiply(a.y)).mod(P)
                .multiply(BigInteger.ONE.add(t).modInverse(P)).mod(P)
            val y = a.y.multiply(b.y).add(a.x.multiply(b.x)).mod(P)
                .multiply(BigInteger.ONE.subtract(t).modInverse(P)).mod(P)
            return Pt(x, y)
        }

        private fun neg(a: Pt): Pt = Pt(P.subtract(a.x), a.y)

        private fun mul(pt: Pt, s: BigInteger): Pt {
            var r = Pt(BigInteger.ZERO, BigInteger.ONE)
            var q = pt
            var v = s
            while (v.signum() > 0) {
                if (v.testBit(0)) r = add(r, q)
                q = add(q, q)
                v = v.shiftRight(1)
            }
            return r
        }
    }
}

/**
 * PeerInfo channel cipher (AOSP pairing_connection /
 * libadb PairingAuthCtx): HKDF-SHA256 (salt = none, info =
 * "adb pairing_auth aes-128-gcm key") derives a 16-byte
 * AES-128-GCM key from the SPAKE2 session key; each direction
 * has its own message counter placed little-endian in the
 * first 8 bytes of a 12-byte IV, both starting at 0.
 */
internal class PairingCipher(keyMaterial: ByteArray) {
    private val key: ByteArray
    private var encryptCounter: Long = 0
    private var decryptCounter: Long = 0

    init {
        val hkdf = HKDFBytesGenerator(SHA256Digest())
        hkdf.init(HKDFParameters(keyMaterial, null, HKDF_INFO))
        val derived = ByteArray(16)
        hkdf.generateBytes(derived, 0, derived.size)
        key = derived
    }

    private fun iv(counter: Long): ByteArray {
        val iv = ByteArray(12)
        var v = counter
        for (i in 0 until 8) {
            iv[i] = (v and 0xFF).toByte()
            v = v shr 8
        }
        return iv
    }

    fun encrypt(plain: ByteArray): ByteArray {
        val cipher = Cipher.getInstance("AES/GCM/NoPadding")
        cipher.init(
            Cipher.ENCRYPT_MODE,
            SecretKeySpec(key, "AES"),
            GCMParameterSpec(GCM_TAG_BITS, iv(encryptCounter++)),
        )
        return cipher.doFinal(plain)
    }

    fun decrypt(encrypted: ByteArray): ByteArray {
        val cipher = Cipher.getInstance("AES/GCM/NoPadding")
        cipher.init(
            Cipher.DECRYPT_MODE,
            SecretKeySpec(key, "AES"),
            GCMParameterSpec(GCM_TAG_BITS, iv(decryptCounter++)),
        )
        return cipher.doFinal(encrypted)
    }

    companion object {
        private val HKDF_INFO =
            "adb pairing_auth aes-128-gcm key".toByteArray(Charsets.UTF_8)
        private const val GCM_TAG_BITS = 128
    }
}

/**
 * One local ADB client instance. [pair] runs the pairing
 * protocol on the pairing port; [connect] establishes the
 * (TLS-upgraded) ADB session on the connect port; [shell] runs
 * one command per stream and returns its full stdout. All step
 * results are reported through [log] verbatim — the settings
 * page's record view is the field-debugging evidence.
 *
 * Not thread-safe by design: the settings page serializes its
 * operations.
 */
class AdbLocal(
    private val keys: AdbKeys,
    private val log: (String) -> Unit,
) {
    private var socket: Socket? = null
    private var input: InputStream? = null
    private var output: OutputStream? = null
    private var plainSocket: Socket? = null

    @Volatile
    var isConnected: Boolean = false
        private set

    private var localIdSeq = (SecureRandom().nextInt(0x01000000) + 1)

    private fun nextLocalId(): Int {
        localIdSeq += 1
        return localIdSeq
    }

    // TLS for both ADB ports uses the ADB identity certificate
    // as the client certificate and accepts any server
    // certificate: authenticity comes from the SPAKE2 pairing
    // and adbd's stored public key, not from PKI (the ADB
    // security model; libadb SslUtils does the same).
    private inner class AdbKeyManager : X509KeyManager {
        override fun getClientAliases(keyType: String?, issuers: Array<out java.security.Principal>?): Array<String> =
            arrayOf(ALIAS)
        override fun chooseClientAlias(
            keyType: Array<out String>?,
            issuers: Array<out java.security.Principal>?,
            socket: Socket?,
        ): String = ALIAS
        override fun getServerAliases(keyType: String?, principals: Array<out java.security.Principal>?): Array<String>? =
            null
        override fun chooseServerAlias(
            keyType: String?,
            principals: Array<out java.security.Principal>?,
            socket: Socket?,
        ): String? = null
        override fun getCertificateChain(alias: String?): Array<X509Certificate> =
            arrayOf(keys.certificate)
        override fun getPrivateKey(alias: String?): PrivateKey = keys.privateKey
    }

    private fun newSslContext(): SSLContext {
        val (ctx, protoName) = try {
            SSLContext.getInstance("TLSv1.3") to "TLSv1.3"
        } catch (e: Exception) {
            log("TLSv1.3 SSLContext 不可用（${e.message}），改用 TLS")
            SSLContext.getInstance("TLS") to "TLS"
        }
        val trustAll = object : X509TrustManager {
            override fun checkClientTrusted(chain: Array<out X509Certificate>?, authType: String?) = Unit
            override fun checkServerTrusted(chain: Array<out X509Certificate>?, authType: String?) = Unit
            override fun getAcceptedIssuers(): Array<X509Certificate> = emptyArray()
        }
        ctx.init(arrayOf(AdbKeyManager()), arrayOf(trustAll), SecureRandom())
        log("SSLContext: $protoName")
        return ctx
    }

    // Wraps the plain socket in TLS (autoClose = false: callers
    // manage the plain socket's lifetime themselves) and runs
    // the handshake.
    private fun wrapTls(plain: Socket, host: String, port: Int): SSLSocket {
        val ctx = newSslContext()
        val ssl = ctx.socketFactory.createSocket(plain, host, port, false) as SSLSocket
        val supported = ssl.supportedProtocols.toList()
        if ("TLSv1.3" in supported) {
            ssl.enabledProtocols = arrayOf("TLSv1.3")
        }
        ssl.startHandshake()
        log("TLS 握手完成：protocol=${ssl.session.protocol}")
        return ssl
    }

    /**
     * TLS exported keying material, 64 bytes (libadb
     * PairingConnectionCtx.exportKeyingMaterial): reflective
     * call into Conscrypt — the platform class on API 29+, the
     * standalone class name as fallback. The exported material
     * is appended to the pairing code to form the SPAKE2
     * password, binding the PAKE to this TLS connection.
     */
    private fun exportKeyingMaterial(ssl: SSLSocket, length: Int): ByteArray {
        if (Build.VERSION.SDK_INT < 29) {
            throw SSLException("TLSv1.3 isn't supported on your platform (API < 29)")
        }
        val errors = mutableListOf<String>()
        for (className in listOf("com.android.org.conscrypt.Conscrypt", "org.conscrypt.Conscrypt")) {
            try {
                val cls = Class.forName(className)
                val method = cls.getMethod(
                    "exportKeyingMaterial",
                    SSLSocket::class.java,
                    String::class.java,
                    ByteArray::class.java,
                    Integer.TYPE,
                )
                return method.invoke(null, ssl, EXPORTED_KEY_LABEL, null, length) as ByteArray
            } catch (e: Exception) {
                errors.add("$className: ${e.cause?.message ?: e.message}")
            }
        }
        throw SSLException("exportKeyingMaterial failed: ${errors.joinToString(" | ")}")
    }

    // ----- pairing (PairingConnectionCtx wire layout) -----

    private fun writePairingPacket(out: OutputStream, type: Int, payload: ByteArray) {
        // PairingPacketHeader: version u8, type u8, payload
        // size u32 BIG-endian (note: unlike the LE ADB header).
        val hdr = ByteBuffer.allocate(6).order(ByteOrder.BIG_ENDIAN)
        hdr.put(PAIRING_VERSION.toByte())
        hdr.put(type.toByte())
        hdr.putInt(payload.size)
        out.write(hdr.array())
        out.write(payload)
        out.flush()
    }

    private fun readPairingPacket(inp: InputStream): Pair<Int, ByteArray> {
        val hdr = readFully(inp, 6)
        val bb = ByteBuffer.wrap(hdr).order(ByteOrder.BIG_ENDIAN)
        val version = bb.get().toInt() and 0xFF
        val type = bb.get().toInt() and 0xFF
        val size = bb.int
        if (version != PAIRING_VERSION) {
            throw IOException("pairing packet version mismatch: $version")
        }
        if (size < 0 || size > PAIRING_MAX_PAYLOAD) {
            throw IOException("pairing packet size out of range: $size")
        }
        return type to readFully(inp, size)
    }

    /**
     * Full pairing exchange on the pairing port: direct TLS
     * (no plaintext CNXN/STLS phase on this port — that dance
     * belongs to the connect port), then SPAKE2 + encrypted
     * PeerInfo inside it. On success adbd stores our public
     * key; the connection is closed immediately afterwards.
     */
    fun pair(host: String, port: Int, code: String) {
        log("配對：連線 $host:$port")
        val plain = Socket()
        plain.connect(InetSocketAddress(host, port), CONNECT_TIMEOUT_MS)
        plain.soTimeout = READ_TIMEOUT_MS
        plain.tcpNoDelay = true
        val ssl = wrapTls(plain, host, port)
        try {
            val out = ssl.outputStream
            val inp = ssl.inputStream
            val exported = exportKeyingMaterial(ssl, EXPORT_KEY_SIZE)
            log("配對：已取得 TLS exported key material（${exported.size} bytes）")
            val password = code.toByteArray(Charsets.UTF_8) + exported
            val spake = Spake2Core(alice = true)
            val privRandom = ByteArray(64)
            SecureRandom().nextBytes(privRandom)
            val myMsg = spake.generateMessage(password, privRandom)
            writePairingPacket(out, PAIRING_SPAKE2_MSG, myMsg)
            log("配對：已送出 SPAKE2 訊息（${myMsg.size} bytes）")
            val (theirType, theirMsg) = readPairingPacket(inp)
            if (theirType != PAIRING_SPAKE2_MSG) {
                throw IOException("pairing: expected SPAKE2_MSG packet, got type $theirType")
            }
            log("配對：已收到裝置 SPAKE2 訊息（${theirMsg.size} bytes）")
            val sessionKey = spake.processMessage(theirMsg)
            val cipher = PairingCipher(sessionKey)
            val peerInfo = ByteArray(PEER_INFO_SIZE)
            peerInfo[0] = PEER_INFO_TYPE_RSA_KEY
            val named = keys.encodeWithName(PEER_INFO_NAME)
            System.arraycopy(named, 0, peerInfo, 1, minOf(named.size, PEER_INFO_SIZE - 1))
            writePairingPacket(out, PAIRING_PEER_INFO, cipher.encrypt(peerInfo))
            log("配對：已送出加密 PeerInfo")
            val (infoType, encInfo) = readPairingPacket(inp)
            if (infoType != PAIRING_PEER_INFO) {
                throw IOException("pairing: expected PEER_INFO packet, got type $infoType")
            }
            val theirInfo = cipher.decrypt(encInfo)
            if (theirInfo.size != PEER_INFO_SIZE) {
                throw IOException("pairing: PeerInfo size ${theirInfo.size}, expected $PEER_INFO_SIZE")
            }
            log("配對：已收到並解密裝置 PeerInfo（type=${theirInfo[0]}）")
        } finally {
            try {
                ssl.close()
            } catch (e: Exception) {
                // closing a failed pairing socket: nothing useful to add
            }
            try {
                plain.close()
            } catch (e: Exception) {
                // same as above
            }
        }
        log("配對成功：裝置已記住本 App 的 ADB 公鑰")
    }

    // ----- connect port session -----

    /**
     * Opens the ADB session on the connect port: plaintext
     * CNXN first, then the STLS upgrade to TLS on the same
     * socket (adbd authenticates us by the client certificate
     * whose public key was paired), then the peer's CNXN over
     * TLS completes the handshake. Plaintext AUTH is answered
     * too, for adbds that ask before offering STLS.
     */
    fun connect(host: String, port: Int) {
        close()
        log("連接：連線 $host:$port")
        val plain = Socket()
        plain.connect(InetSocketAddress(host, port), CONNECT_TIMEOUT_MS)
        plain.soTimeout = READ_TIMEOUT_MS
        plain.tcpNoDelay = true
        plainSocket = plain
        var inp: InputStream = plain.inputStream
        var out: OutputStream = plain.outputStream
        input = inp
        output = out
        socket = plain
        val version = AdbProtocol.versionForSdk()
        val maxData = AdbProtocol.maxDataForSdk()
        writeAdbMessage(out, AdbProtocol.A_CNXN, version, maxData, CNXN_PAYLOAD)
        log("連接：已送出 CNXN（version=0x%08x, maxdata=%d）".format(version, maxData))
        var signatureSent = false
        var upgraded = false
        while (true) {
            val msg = readAdbMessage(inp)
            when (msg.command) {
                AdbProtocol.A_CNXN -> {
                    val banner = msg.payload.decodeToString().trimEnd('\u0000')
                    log("連接：收到裝置 CNXN：$banner")
                    isConnected = true
                    return
                }
                AdbProtocol.A_STLS -> {
                    if (upgraded) throw IOException("connect: duplicate STLS")
                    log("連接：收到 STLS，升級 TLS")
                    writeAdbMessage(out, AdbProtocol.A_STLS, AdbProtocol.A_STLS_VERSION, 0, null)
                    val ssl = wrapTls(plain, host, port)
                    inp = ssl.inputStream
                    out = ssl.outputStream
                    input = inp
                    output = out
                    socket = ssl
                    upgraded = true
                }
                AdbProtocol.A_AUTH -> {
                    when (msg.arg0) {
                        AdbProtocol.AUTH_TOKEN -> {
                            if (!signatureSent) {
                                val sig = keys.authSign(msg.payload)
                                writeAdbMessage(out, AdbProtocol.A_AUTH, AdbProtocol.AUTH_SIGNATURE, 0, sig)
                                signatureSent = true
                                log("連接：已回覆 AUTH SIGNATURE")
                            } else {
                                writeAdbMessage(
                                    out, AdbProtocol.A_AUTH, AdbProtocol.AUTH_RSAPUBLICKEY, 0,
                                    keys.encodeWithName(PEER_INFO_NAME),
                                )
                                log("連接：簽章未被接受，已改送 AUTH RSAPUBLICKEY")
                            }
                        }
                        AdbProtocol.AUTH_RSAPUBLICKEY -> {
                            writeAdbMessage(
                                out, AdbProtocol.A_AUTH, AdbProtocol.AUTH_RSAPUBLICKEY, 0,
                                keys.encodeWithName(PEER_INFO_NAME),
                            )
                            log("連接：已回覆 AUTH RSAPUBLICKEY")
                        }
                        else -> throw IOException("connect: unexpected AUTH type ${msg.arg0}")
                    }
                }
                AdbProtocol.A_CLSE -> throw IOException("connect: peer closed the connection (CLSE)")
                else -> log("連接：忽略訊息 ${msg.commandName()} arg0=${msg.arg0} arg1=${msg.arg1}")
            }
        }
    }

    // ----- shell streams -----

    /**
     * Runs one shell command on a fresh stream and returns its
     * full stdout (AdbStream semantics: OPEN "shell:<cmd>",
     * ack every WRTE with OKAY, finish on CLSE). The caller is
     * responsible for trimming; output is returned verbatim.
     */
    fun shell(command: String): String {
        if (!isConnected) throw IOException("shell: not connected")
        val inp = input ?: throw IOException("shell: no input stream")
        val out = output ?: throw IOException("shell: no output stream")
        val localId = nextLocalId()
        val destination = "shell:$command\u0000".toByteArray(Charsets.UTF_8)
        writeAdbMessage(out, AdbProtocol.A_OPEN, localId, 0, destination)
        var remoteId = -1
        var opened = false
        val result = ByteArrayOutputStream()
        while (true) {
            val msg = readAdbMessage(inp)
            when (msg.command) {
                AdbProtocol.A_OKAY -> {
                    if (msg.arg1 == localId) {
                        remoteId = msg.arg0
                        opened = true
                    }
                }
                AdbProtocol.A_WRTE -> {
                    if (msg.arg1 == localId) {
                        result.write(msg.payload)
                        writeAdbMessage(out, AdbProtocol.A_OKAY, localId, remoteId, null)
                    }
                }
                AdbProtocol.A_CLSE -> {
                    if (msg.arg1 == localId) {
                        if (!opened) {
                            throw IOException("shell: stream refused (CLSE) for: $command")
                        }
                        writeAdbMessage(out, AdbProtocol.A_CLSE, localId, remoteId, null)
                        return result.toString(Charsets.UTF_8.name())
                    }
                }
                else -> log("shell：忽略訊息 ${msg.commandName()} arg0=${msg.arg0} arg1=${msg.arg1}")
            }
        }
    }

    fun close() {
        isConnected = false
        try {
            socket?.close()
        } catch (e: Exception) {
            // already gone
        }
        try {
            plainSocket?.close()
        } catch (e: Exception) {
            // already gone
        }
        socket = null
        plainSocket = null
        input = null
        output = null
    }

    companion object {
        private const val ALIAS = "adb"
        private const val CONNECT_TIMEOUT_MS = 10_000
        private const val READ_TIMEOUT_MS = 10_000
        private const val EXPORT_KEY_SIZE = 64
        private const val EXPORTED_KEY_LABEL = "adb-label\u0000"
        private const val PEER_INFO_NAME = "PaxVM"
        private const val PEER_INFO_TYPE_RSA_KEY: Byte = 0
        private const val PEER_INFO_SIZE = 8192
        private const val PAIRING_VERSION = 1
        private const val PAIRING_SPAKE2_MSG = 0
        private const val PAIRING_PEER_INFO = 1
        private const val PAIRING_MAX_PAYLOAD = 2 * PEER_INFO_SIZE
        private val CNXN_PAYLOAD = "host::\u0000".toByteArray(Charsets.UTF_8)
    }
}

