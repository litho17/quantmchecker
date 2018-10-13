package simplevote_1.com.cyberpointllc.stac;

import org.apache.commons.codec.binary.Base64;

import java.nio.charset.StandardCharsets;

public class DESHelper {
    public static String grabEncryptedString(String message, String key) {
        byte[] messageBytes = message.getBytes(StandardCharsets.UTF_8);
        byte[] encryptedBytes = DES.encrypt(messageBytes, key);
        return Base64.encodeBase64URLSafeString(encryptedBytes);
    }
}
