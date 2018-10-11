package battleboats_1.com.cyberpointllc.stac.numerical;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;

public class CryptoUtil {
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
        byte[] report = dataInt.toByteArray();

        if (report[0] == 0 && report.length > bitSize) {
            // got an extra byte, get rid of it
            byte[] tmp = new byte[report.length - 1];
            System.arraycopy(report, 1, tmp, 0, tmp.length);
            return tmp;
        }

        if (report.length < bitSize) {
            // less data than usual, pad
            byte[] tmp = new byte[bitSize];
            System.arraycopy(report, 0, tmp, tmp.length - report.length, report.length);
            return tmp;
        }
        return report;
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

    public static byte[] decrypt(byte[] data, CryptoPrivateKey privateKey, int trimToSize) {
        return stripPadding(privateKey.decryptBytes(data), trimToSize);
    }

    public static byte[] sign(byte[] data, CryptoPrivateKey privateKey) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(data);
            byte[] sig = privateKey.decryptBytes(hash);

            return sig;
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Validates the signature on data
     *
     * @param data      the data to validate
     * @param sig       the signature on the data
     * @param publicKey the public key to use for validation
     * @return true if the signature matches the data
     */
    public static boolean validateSig(byte[] data, byte[] sig, CryptoPublicKey publicKey) {
        MessageDigest digest = null;
        try {
            digest = MessageDigest.getInstance("SHA-256");
            byte[] expectedHash = digest.digest(data);
            byte[] providedHash = CryptoUtil.stripPadding(publicKey.encryptBytes(sig), expectedHash.length);
            return Arrays.equals(expectedHash, providedHash);
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }
}
