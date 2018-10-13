package simplevote_1.com.cyberpointllc.stac.algorithm;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;

public class CipherUtil {
    public static BigInteger toBigInt(byte[] data, int bitSize) {
        // from https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/crypto/engines/RSACoreEngine.java
        if (data.length > bitSize + 1) {
            throw new IllegalArgumentException("data length " + data.length + " is too long for bitsize " + bitSize);
        }

        return new BigInteger(1, data);
    }

    public static BigInteger toBigInt(byte[] data) {
        return new BigInteger(1, data);
    }

    public static byte[] fromBigInt(BigInteger dataInt, int bitSize) {
        // from https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/crypto/engines/RSACoreEngine.java
        byte[] outcome = dataInt.toByteArray();

        if (outcome[0] == 0 && outcome.length > bitSize) {
            // got an extra byte, get rid of it
            byte[] tmp = new byte[outcome.length - 1];
            System.arraycopy(outcome, 1, tmp, 0, tmp.length);
            return tmp;
        }

        if (outcome.length < bitSize) {
            // less data than usual, pad
            return new CipherUtilHelp(bitSize, outcome).invoke();
        }
        return outcome;
    }

    /**
     * encryption may pad the result to a multiple of the bitsize, this will trim it back down
     *
     * @param ptBytes padded bytes
     * @param length  expected length
     * @return bytes array of stripped bytes
     */
    public static byte[] stripPadding(byte[] ptBytes, int length) {
        int diff = ptBytes.length - length;
        return Arrays.copyOfRange(ptBytes, diff, ptBytes.length);
    }

    /**
     * Encrypts the data with the specified public key
     *
     * @param data      to encrypt
     * @param publicKey used to encrypt the data
     * @return byte array of the encrypted data
     */
    public static byte[] encrypt(byte[] data, CipherPublicKey publicKey) {
        return publicKey.encryptBytes(data);
    }

    public static byte[] decrypt(byte[] data, CipherPrivateKey privateKey, int trimToSize) {
        return stripPadding(privateKey.decryptBytes(data), trimToSize);
    }

    public static byte[] sign(byte[] data, CipherPrivateKey privateKey) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(data);
            byte[] sig = privateKey.decryptBytes(hash);

            return sig;
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    private static class CipherUtilHelp {
        private int bitSize;
        private byte[] outcome;

        public CipherUtilHelp(int bitSize, byte[] outcome) {
            this.bitSize = bitSize;
            this.outcome = outcome;
        }

        public byte[] invoke() {
            byte[] tmp = new byte[bitSize];
            System.arraycopy(outcome, 0, tmp, tmp.length - outcome.length, outcome.length);
            return tmp;
        }
    }
}
