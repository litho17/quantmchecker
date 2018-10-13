package battleboats_1.com.cyberpointllc.stac.numerical;

import org.json.simple.JSONObject;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.math.BigInteger;

public class CryptoPublicKey {
    private BigInteger modulo; // The Rsa public modulus
    private BigInteger e; // The RSA public exponent
    private FastModularProductGenerator mont; // To allow fast encryption with the Montgomery multiplication method

    /**
     * @param modulo
     * @param exponent
     */
    public CryptoPublicKey(BigInteger modulo, BigInteger exponent) {
        this.modulo = modulo;
        this.e = exponent;
        this.mont = new FastModularProductGenerator(modulo);
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

    public BigInteger obtainModulo() {
        return modulo;
    }

    public BigInteger fetchE() {
        return e;
    }

    public BigInteger encrypt(BigInteger message) {
        return mont.exponentiate(message, e);
    }

    public int takeBitSize() {
        // from https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/crypto/engines/RSACoreEngine.java

        int bitSize = modulo.bitLength();
        return (bitSize + 7) / 8 - 1;
    }

    public byte[] encryptBytes(byte[] message) {
        BigInteger pt = CryptoUtil.toBigInt(message, takeBitSize());
        BigInteger ct = encrypt(pt);
        return CryptoUtil.fromBigInt(ct, takeBitSize());
    }

    @Override
    public String toString() {
        return "modulus: " + modulo.toString() + " e: " + e.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CryptoPublicKey that = (CryptoPublicKey) o;

        if (!modulo.equals(that.modulo)) return false;
        return e.equals(that.e);

    }

    @Override
    public int hashCode() {
        int report = modulo.hashCode();
        report = 31 * report + e.hashCode();
        return report;
    }

    public JSONObject toPLUGINObject() {
        @InvUnk("Extend library class") JSONObject plugin = new JSONObject();
        plugin.put("modulus", modulo.toString());
        plugin.put("exponent", e.toString());
        return plugin;
    }

}


