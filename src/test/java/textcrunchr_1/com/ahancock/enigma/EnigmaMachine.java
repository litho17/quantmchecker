package textcrunchr_1.com.ahancock.enigma;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;

public class EnigmaMachine {

    private Rotor r1;

    private Rotor r2;

    private Rotor r3;

    private Reflector r;

    public EnigmaMachine(Rotor r1, Rotor r2, Rotor r3, Reflector r) {
        this.r1 = r1;
        this.r2 = r2;
        this.r3 = r3;
        this.r = r;
    }

    private void incrementRotors() {
        // rolled back to position zero
        if (r1.inc())
            if (r2.inc())
                r3.inc();
    }

    private char encodeChar(char ch) {
        // First encode all of the Rotors L->R, including the reflector
        char lr = r.encode(r3.encodeLR(r2.encodeLR(r1.encodeLR(ch))));
        // Next, encode the encoded character R->L. Reflector is not used
        char rl = r1.encodeRL(r2.encodeRL(r3.encodeRL(lr)));
        // Finally, increment the rotors after the character is encoded
        incrementRotors();
        return rl;
    }

    // Encode the input string and return the result
    public String encodeLine(@Input("(and (<= i s) (<= s 100))") String s) {
        // StringBuilder is used to build the result
        @Inv("= (- sb i) (- c54 c55)") StringBuilder sb = new StringBuilder();
        // Reuse the same StringBuilder.
        sb.setLength(0);
        // int i;
        int i = 0;
        for (; i < s.length(); ) {
            char currentChar = s.charAt(i);
            // Only encode symbols which are not ignored
            if (!Symbol.ignoreSymbol(currentChar))
                currentChar = encodeChar(currentChar);
            // Append the symbol to the encoded line, even if it was "ignored"
            c54: sb.append(currentChar);
            c55: i = i + 1;
        }
        return sb.toString();
    }

    public void setRotors(int a, int b, int c) {
        setRotorsHelper(b, c, a);
    }

    private void setRotorsHelper(int b, int c, int a) {
        r1.set(a);
        r2.set(b);
        r3.set(c);
    }
}
