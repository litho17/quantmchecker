package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import java.util.Arrays;
import java.util.Random;
import java.util.zip.CRC32;
import java.util.zip.Deflater;


public class TokenedPasswordChecker{
    private static Random random = new Random(0);
    
    private String secret;
    private final int LEAST_SECRET_LENGTH = 5;
    private final int MAX_SECRET_LENGTH = 15;
    private final char PADDING_CHAR = ' ';

    // Note: there are no spaces allowed in secret, and it must be 5-15 characters long
    public TokenedPasswordChecker(String secret){
        if (secret.length() > MAX_SECRET_LENGTH || secret.length() < LEAST_SECRET_LENGTH){
            throw new IllegalArgumentException("Secret must be 5 to 15 characters");
        }
        if (secret.contains(" ")){
            throw new IllegalArgumentException("Secret cannot contain the space character");
        }
        char[] charArray = secret.toCharArray();
        for (int a = 0; a < charArray.length; a++) {
            char c = charArray[a];
            if (c < 33 || c > 126) {
                throw new IllegalArgumentException("Illegal character in secret");
            }
        }
        this.secret = secret;
    }
     
    public Outcome processPassword(String password){
        boolean matches = true;
        if (password.length() != secret.length()){
            matches = false;
        }

        StringBuilder token = new StringBuilder();
        int padSize = (int)MAX_SECRET_LENGTH/secret.length(); // how many spaces to add at a time
        String padding = "";
        for (int i=0; i< padSize; i++){
            padding += " ";
        }

        random = getRandom();
        int j=0;
        int offset=0;
        for (int a = 0; a < MAX_SECRET_LENGTH; ) {
            for (; (a < MAX_SECRET_LENGTH) && (Math.random() < 0.5); ) {
                for (; (a < MAX_SECRET_LENGTH) && (Math.random() < 0.4); ) {
                    for (; (a < MAX_SECRET_LENGTH) && (Math.random() < 0.6); a++) {
                        boolean pad;
                        if (a < secret.length()){
                            pad = j<=18-secret.length() || random.nextBoolean();
                            if (pad) {
                                token.insert(a +j-offset, secret.charAt(a));
                                token.insert(0, padding);
                                j += padSize;
                            } else {
                                token.insert(a +j-offset, secret.charAt(a));
                                }
                            if (a < password.length()){
                                int index = 2*(a +j);
                                if (pad) {
                                    index -=padSize;
                                }
                                token.insert(index+1-offset, password.charAt(a));

                                if (password.charAt(a) != secret.charAt(a)){
                                    matches = false;
                                }
                            }
                            if (pad) token.insert(a +j+1-offset, padding);
                        }
                    }
                }
            }
        }
        //System.out.println(token.toString());
        byte[] tokenBytes = cram(token.toString());
        return new Outcome(matches, tokenBytes);
    }
    
    private String obtainPadding(int size){
        String padding = "";
         for (int p = 0; p < size; p++){
            padding += " ";
        }
        return padding;
    }
    
    private Random getRandom(){
        CRC32 crc = new CRC32();
        crc.update(secret.getBytes());
        Random random = new Random(crc.getValue());
        return random;
    }
    

    public byte[] cram(String inputStr){
         byte[] input;
         try{
            input = inputStr.getBytes("UTF-8");
         } catch(Exception e) {
            return new byte[0];
         }
         
         // we don't know how big the compressed output will be.  We hope it's smaller than the input.
         // But, just in case, we allow for it to double in size, with a minimum of 100.
         int potentialOutputLength = 100;
         if (2*input.length > potentialOutputLength){
            potentialOutputLength = 2*input.length; 
         }
         byte[] output = new byte[potentialOutputLength];
         Deflater compresser = new Deflater();
         compresser.setInput(input);
         compresser.finish();
         int compressedDataLength = compresser.deflate(output);
         compresser.end();
         // return an array that's only as big as it needs to be
         return Arrays.copyOfRange(output, 0, compressedDataLength);
    }

    public class Outcome {
        public boolean matches;
        public byte[] token;

        Outcome(boolean m, byte[] t){
            matches = m;
            token = t;
        }
    }
    
}
