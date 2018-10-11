package braidit_1.com.cyberpointllc.stac.mathematic;

import braidit_1.com.cyberpointllc.stac.jack.direct.OBJNOTEObject;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.OBJNOTEParser;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.ParseException;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.math.BigInteger;

public class CryptoSystemPublicKey {
    private BigInteger divisor; // The Rsa public modulus
    private BigInteger e; // The RSA public exponent
    private MgProductGenerator mont; // To allow fast encryption with the Montgomery multiplication method

    /**
     * @param divisor
     * @param exponent
     */
    public CryptoSystemPublicKey(BigInteger divisor, BigInteger exponent) {
        this.divisor = divisor;
        this.e = exponent;
        this.mont = new MgProductGenerator(divisor);
    }

    /**
     * Encrypts the data with the specified public key
     *
     * @param data      to encrypt
     * @return byte array of the encrypted data
     */
    public byte[] encrypt(byte[] data) {
        return encryptBytes(data);
    }

    public BigInteger obtainDivisor() {
        return divisor;
    }

    public BigInteger getE() {
        return e;
    }

    public BigInteger encrypt(BigInteger message) {
        return mont.exponentiate(message, e);
    }

    public int obtainBitSize() {
        // from https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/crypto/engines/RSACoreEngine.java

        int bitSize = divisor.bitLength();
        return (bitSize + 7) / 8 - 1;
    }

    public byte[] encryptBytes(byte[] message) {
        BigInteger pt = CryptoSystemUtil.toBigInt(message, obtainBitSize());
        BigInteger ct = encrypt(pt);
        return CryptoSystemUtil.fromBigInt(ct, obtainBitSize());
    }

    @Override
    public String toString() {
        return "modulus: " + divisor.toString() + " e: " + e.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CryptoSystemPublicKey that = (CryptoSystemPublicKey) o;

        if (!divisor.equals(that.divisor)) return false;
        return e.equals(that.e);

    }

    @Override
    public int hashCode() {
        int report = divisor.hashCode();
        report = 31 * report + e.hashCode();
        return report;
    }

    public OBJNOTEObject toOBJNOTEObject() {
        @InvUnk("Extend library class") OBJNOTEObject objnote = new OBJNOTEObject();
        objnote.put("modulus", divisor.toString());
        objnote.put("exponent", e.toString());
        return objnote;
    }

    public static CryptoSystemPublicKey fromObjnote(OBJNOTEObject publicKeyObjnote) {
        BigInteger divisor = new BigInteger((String) publicKeyObjnote.get("modulus"));
        BigInteger exponent = new BigInteger((String) publicKeyObjnote.get("exponent"));
        return new CryptoSystemPublicKey(divisor, exponent);
    }
}


