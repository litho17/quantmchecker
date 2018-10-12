package calculator_1.com.cyberpointllc.stac;

import org.apache.commons.codec.binary.Base64;

import java.nio.charset.StandardCharsets;

public class DESAssistant {
    public static String pullEncryptedString(String message, String code) {
        byte[] messageBytes = message.getBytes(StandardCharsets.UTF_8);
        byte[] encryptedBytes = DES.encrypt(messageBytes, code);
        return Base64.encodeBase64URLSafeString(encryptedBytes);
    }
}
