package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.ahancock.enigma.EnigmaFactory;
import textcrunchr_1.com.ahancock.enigma.EnigmaMachine;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class EnigmaProcessor extends Processor {

    private static final String NAME = "enigma";

    public TCResult process(@Input("") InputStream inps) throws IOException {
        // read to string
        @Inv("<= br inps") InputStreamReader is = new InputStreamReader(inps);
        @Inv("= (- sb br) (- c24 c22 c25)") StringBuilder sb = new StringBuilder();
        BufferedReader br = new BufferedReader(is);
        String read;
        c22: read = br.readLine();
        while (read != null) {
            c24: sb.append(read);
            c25: read = br.readLine();
        }
        String theString = sb.toString().toUpperCase();
        // Construct the machine
        EnigmaMachine machine = EnigmaFactory.buildEnigmaMachine();
        // Set the rotors, encrypt the string and print the results
        machine.setRotors(5, 9, 14);
        String encodedString = machine.encodeLine(theString);
        String name = "Enigma transformation (5, 9, 14)";
        String value = encodedString;
        return new TCResult(name, value);
    }

    public String getName() {
        return NAME;
    }
}
