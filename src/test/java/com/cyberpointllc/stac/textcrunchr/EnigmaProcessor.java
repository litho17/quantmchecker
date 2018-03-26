package com.cyberpointllc.stac.textcrunchr;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import com.ahancock.enigma.EnigmaFactory;
import com.ahancock.enigma.EnigmaMachine;
import plv.colorado.edu.quantmchecker.qual.ListInv;
import plv.colorado.edu.quantmchecker.qual.Summary;

class EnigmaProcessor extends Processor {

    private static final String NAME = "enigma";

    public TCResult process(InputStream inps) throws IOException {
        // read to string
        InputStreamReader is = new  InputStreamReader(inps);
        @ListInv("<self>+rem(br)=-c20+c22-c23") StringBuilder sb = new  StringBuilder();
        BufferedReader br = new  BufferedReader(is);
        String read = br.readLine();
        while (read != null) {
            sb.append(read);
            read = br.readLine();
        }
        String theString = sb.toString().toUpperCase();
        // Construct the machine
        @ListInv("machine.sb+rem(theString)=encodeLine.c52-encodeLine.c46") EnigmaMachine machine = EnigmaFactory.buildEnigmaMachine();
        // Set the rotors, encrypt the string and print the results
        machine.setRotors(5, 9, 14);
        String encodedString = machine.encodeLine(theString);
        String name = "Enigma transformation (5, 9, 14)";
        String value = encodedString;
        return new  TCResult(name, value);
    }

    public String getName() {
        return NAME;
    }
}
