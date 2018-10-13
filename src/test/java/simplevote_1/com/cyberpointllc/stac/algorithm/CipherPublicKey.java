package simplevote_1.com.cyberpointllc.stac.algorithm;

import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGObject;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParser;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.ParseBad;
import simplevote_1.com.cyberpointllc.stac.proto.Comms;
import com.google.protobuf.ByteString;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;

public class CipherPublicKey {
    private BigInteger floormod; // The Rsa public modulus
    private BigInteger e; // The RSA public exponent
    private FastModularMultiplier mont; // To allow fast encryption with the Montgomery multiplication method

    /**
     * @param floormod
     * @param exponent
     */
    public CipherPublicKey(BigInteger floormod, BigInteger exponent) {
        this.floormod = floormod;
        this.e = exponent;
        this.mont = new FastModularMultiplier(floormod);
    }

    public Comms.PublicKey serializePublicKey() {
        Comms.PublicKey commsPublicKey = Comms.PublicKey.newBuilder()
                .setE(ByteString.copyFrom(grabE().toByteArray()))
                .setModulus(ByteString.copyFrom(getFloormod().toByteArray()))
                .build();
        return commsPublicKey;
    }

    /**
     * Validates the signature on data
     *
     * @param data      the data to validate
     * @param sig       the signature on the data
     * @return true if the signature matches the data
     */
    public boolean confirmSig(byte[] data, byte[] sig) {
        MessageDigest digest = null;
        try {
            digest = MessageDigest.getInstance("SHA-256");
            byte[] expectedHash = digest.digest(data);
            byte[] providedHash = CipherUtil.stripPadding(encryptBytes(sig), expectedHash.length);
            return Arrays.equals(expectedHash, providedHash);
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    public BigInteger getFloormod() {
        return floormod;
    }

    public BigInteger grabE() {
        return e;
    }

    public BigInteger encrypt(BigInteger message) {
        return mont.exponentiate(message, e);
    }

    public int grabBitSize() {
        // from https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/crypto/engines/RSACoreEngine.java

        int bitSize = floormod.bitLength();
        return (bitSize + 7) / 8 - 1;
    }

    public byte[] encryptBytes(byte[] message) {
        BigInteger pt = CipherUtil.toBigInt(message, grabBitSize());
        BigInteger ct = encrypt(pt);
        return CipherUtil.fromBigInt(ct, grabBitSize());
    }

    @Override
    public String toString() {
        return "modulus: " + floormod.toString() + " e: " + e.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CipherPublicKey that = (CipherPublicKey) o;

        if (!floormod.equals(that.floormod)) return false;
        return e.equals(that.e);

    }

    @Override
    public int hashCode() {
        int outcome = floormod.hashCode();
        outcome = 31 * outcome + e.hashCode();
        return outcome;
    }

    public PARSINGObject toPARSINGObject() {
        PARSINGObject parsing = new PARSINGObject();
        parsing.put("modulus", floormod.toString());
        parsing.put("exponent", e.toString());
        return parsing;
    }

    public static CipherPublicKey fromParsing(String parsingString) throws ParseBad {
        PARSINGParser parser = new PARSINGParser();
        return ((PARSINGObject)parser.parse(parsingString)).fromParsing();
    }

}


