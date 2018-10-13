package simplevote_1.com.cyberpointllc.stac.wrapper;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.List;
import java.util.Random;


/******************************************************************************
 *  Compilation:  javac LZW.java
 *  Execution:    java LZW - < input.txt   (compress)
 *  Execution:    java LZW + < input.txt   (expand)
 *  Dependencies: BinaryIn.java BinaryOut.java
 *
 *  Compress or expand binary input from standard input using LZW.
 *
 *  WARNING: STARTING WITH ORACLE JAVA 6, UPDATE 7 the SUBSTRING
 *  METHOD TAKES TIME AND SPACE LINEAR IN THE SIZE OF THE EXTRACTED
 *  SUBSTRING (INSTEAD OF CONSTANT SPACE AND TIME AS IN EARLIER
 *  IMPLEMENTATIONS).
 *
 *  See <a href = "http://java-performance.info/changes-to-string-java-1-7-0_06/">this article</a>
 *  for more details.
 *
 ******************************************************************************/

/**
 * 
 *  The <tt>LZW</tt> class provides static methods for compressing
 *  and expanding a binary input using LZW compression over the 8-bit extended
 *  ASCII alphabet with 12-bit codewords.
 *  <p>
 *  
 *  From http://algs4.cs.princeton.edu/55compression/LZW.java.html
 *  Licensed under the GNU General Public License, version 3 (GPLv3).
 *  
 *  For additional documentation,
 *  see <a href="http://algs4.cs.princeton.edu/55compress">Section 5.5</a> of
 *  <i>Algorithms, 4th Edition</i> by Robert Sedgewick and Kevin Wayne.
 *
 *  @author Robert Sedgewick  
 *  @author Kevin Wayne
 *
 *  modifications by CyberPoint 2015-2017, to allow non-standard tries for compression, try-with-resources
 */
public class LZW {
    private static final int R = 256;       // number of input chars
    private static final int L = 2048;//4096;       // number of codewords = 2^W
    private static final int W = 11; //12;         // codeword width


    // Do not instantiate.
    private LZW() { }

	/**
	 * Make trie containing the provided word and all individual characters
	 * @param words
	 * @return
	 */
    public static TST<Integer> makeTrie(String word){
        TST<Integer> st = new TST<Integer>();
        for (int k = 0; k < R; k++)
            st.place("" + (char) k, k);
        int code = R+1;
        st.place(word, code);
        return st;
    }

    /**
     * Make trie containing the provided words and all individual characters
     * @param words
     * @return
     */
    public static TST<Integer> makeTrieFromList(List<String> words){

        TST<Integer> st = new TST<Integer>();
        for (int q = 0; q < R; q++)
            st.place("" + (char) q, q);
        int code = R+1;
        for (int c = 0; c < words.size(); c++) {
            String word = words.get(c);
            if (code >= L) {
                System.out.println("L is too big: " + L);
            } else {
                st.place(word, code++);
            }
        }
        return st;
    }

	/**
	 * Make trie with progressively longer strings from input.  This is the normal LZW way of doing things
	 * @param input
	 * @return
	 */
    public static TST<Integer> makeTrieFromText(String input){
        	TST<Integer> st = new TST<Integer>();
	        for (int a = 0; a < R; a++)
	            st.place("" + (char) a, a);
	        int code = R+1;
	        while (input.length() > 0) {
	            String s = st.longestPrefixOf(input);  // Find max prefix match s.
	            int t = s.length();
	            if (t < input.length() && code < L) {   // Add s to symbol table.
	                String subst = input.substring(0, t + 1);
	                st.place(subst, code++);
	            }
	            input = input.substring(t);
	        }
	        return st;
    }
    
    public static byte[] cram(TST<Integer> trie, String input){
    
        try(ByteArrayOutputStream bos = new ByteArrayOutputStream();
            DataOutputStream dos = new DataOutputStream(bos);){
            while (input.length() > 0) {
	            String s = trie.longestPrefixOf(input);  // Find max prefix match s.
	            dos.writeInt(trie.fetch(s));      // Write s's encoding.
	            int t = s.length();
	            input = input.substring(t);     // Scan past s in input.
	        }
            dos.writeInt(R);
            dos.flush();
            SmashingObject obj = new SmashingObject(trie, bos.toByteArray());
            try(
                ByteArrayOutputStream objBytes = new ByteArrayOutputStream();
                ObjectOutputStream oos = new ObjectOutputStream(objBytes);) {
                oos.writeObject(obj);
                return objBytes.toByteArray();
            }
	    }
	    catch(Exception e){
	        e.printStackTrace();
	        return new byte[0];
	    }
    }
    
    /**
     * Reads a sequence of 8-bit bytes from standard input; compresses
     * them using LZW compression with 12-bit codewords;
     */
    public static byte[] cram(String file) {
        try(ByteArrayOutputStream bos = new ByteArrayOutputStream();
        	    DataOutputStream dos = new DataOutputStream(bos) ){
        	String input = readFile(file);
        	Random random = new Random();
        	random.setSeed(0);

	        //PrefixThing st = new PrefixThing();
        	TST<Integer> st = new TST<Integer>();
	        for (int k = 0; k < R; k++)
	            st.place("" + (char) k, k);
	        int code = R+1;  // R is codeword for EOF
	
	        while (input.length() > 0) {
	            String s = st.longestPrefixOf(input);  // Find max prefix match s.
	            dos.writeInt(st.fetch(s));      // Print s's encoding.
	            int t = s.length();
	            if (t < input.length() && code < L) {   // Add s to symbol table.
	                st.place(input.substring(0, t + 1), code++);
	            }
	            input = input.substring(t);            // Scan past s in input.
	        }
	
	        dos.writeInt(R);
	        dos.flush();

	        return bos.toByteArray();
	      
        }
        catch(IOException e){
        	System.out.println(e);
        	return new byte[0];
        }
    }

    // compression returns a byte[] representation of both the trie and the compressed text.  this pulls out the trie
    public static TST<Integer> readTrie(byte[] bytes) throws IOException{
       try(ObjectInputStream ois = new ObjectInputStream(new ByteArrayInputStream(bytes))){
           try{
              SmashingObject obj = (SmashingObject) ois.readObject();
              return obj.trie;
           } catch (ClassNotFoundException e){
               System.err.println("error reading object");
               throw new IOException(e);
           }
	    }
    }

    // compression returns a byte[] representation of both the trie and the compressed text.  this pulls out the text
    public static byte[] readCompressedData(byte[] bytes) throws IOException{
        try(ObjectInputStream ois = new ObjectInputStream(new ByteArrayInputStream(bytes))){
            try{
                SmashingObject obj = (SmashingObject) ois.readObject();
                return obj.compressedData;
            } catch (ClassNotFoundException e){
                System.err.println("error reading object");
                throw new IOException(e);
            }
        }
    }

    public static String decompress(byte[] buff, TST<Integer> trie) {
        StringBuilder outcome = new StringBuilder();
        try(ByteArrayInputStream bis = new ByteArrayInputStream(buff)){
            DataInputStream dis = new DataInputStream(bis);

            String[] st = new String[L];

            // fill st from trie
            for (String key : trie.keys()) {
               int code = trie.fetch(key);
               st[code] = key;
            }

            int codeword = dis.readInt();
            System.out.println("codeword " + codeword);
            if (codeword == R) return outcome.toString();           // expanded message is empty string
            String val = st[codeword];

            while (true) {
                outcome.append(val);
                codeword = dis.readInt();
                if (codeword == R) break;
                val = st[codeword];
            }
        }
        catch(IOException e){
            System.out.println(e);
        }
        return outcome.toString();
    }

    /**
     * Reads a sequence of bit encoded using LZW compression with
     * codewords in buff; expands them; and returns
     * the results.
     */
    public static String decompress(byte[] buff) {
    	StringBuilder outcome = new StringBuilder();
    	try(ByteArrayInputStream bis = new ByteArrayInputStream(buff);
    		DataInputStream dis = new DataInputStream(bis);){
    		
	        String[] st = new String[L];
	        int c; // next available codeword value
	
	        // initialize symbol table with all 1-character strings
	        for (c = 0; c < R; c++)
	            st[c] = "" + (char) c;
	        st[c++] = "";                        // (unused) lookahead for EOF
	
	        int codeword = dis.readInt();
	        if (codeword == R) return outcome.toString();           // expanded message is empty string
	        String val = st[codeword];
	
	        while (true) {
	            outcome.append(val);
	            codeword = dis.readInt();
	            if (codeword == R) break;
	            String s = st[codeword];
	            if (c == codeword) s = val + val.charAt(0);   // special case hack
	            if (c < L) st[c++] = val + s.charAt(0);
	            val = s;
	        }
    	}
    	catch(IOException e){
    		System.out.println(e);
    	}
    	return outcome.toString();
    }
    
    private static String readFile(String file) throws IOException{
    	BufferedReader reader = new BufferedReader(new FileReader(file));
        String line = null;
        StringBuilder stringCreator = new StringBuilder();
        String ls = System.getProperty("line.separator");

        while( ( line = reader.readLine() ) != null ) {
            stringCreator.append(line);
            stringCreator.append(ls);
        }

        return stringCreator.toString();
    }

    
    /*
       Notes:   What works: 
       1. if I put in "aaabac", then compressing those strings (aa, ab, ac" takes about 60 K nanoseconds, while compressing "ad" takes 110K nanoseconds
       2. Put in "aaabacbabbbccacb" then cc has same property
       

    */
    public static class SmashingObject implements Serializable{
        TST<Integer> trie;
        byte[] compressedData;

        SmashingObject(TST<Integer> trie, byte[] compressedBytes){
            this.trie = trie;
            this.compressedData = compressedBytes;
        }
    }

}


