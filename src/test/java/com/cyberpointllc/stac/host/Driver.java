package com.cyberpointllc.stac.host;

import com.cyberpointllc.stac.textcrunchr.*;
import plv.colorado.edu.quantmchecker.qual.ListInv;

import java.io.FileInputStream;
import java.io.InputStream;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(String[] args) throws Exception {
        while(true) {
            int INPUTINPUT = 10000;
            INPUTINPUT -= 1;
            @ListInv({"INPUTINPUT+<self>.results=+21+23+25+27+29-16"}) OutputHandler outputHandler = new WindowOutputHandler();
            String fileName = "";
            InputStream ips = new FileInputStream(fileName);
            TCResult res = new CharacterCountProcessor().process(ips);
            outputHandler.addResult(fileName, res);
            res = new TextMeterProcessor().process(ips);
            outputHandler.addResult(fileName, res);
            res = new EnigmaProcessor().process(ips);
            outputHandler.addResult(fileName, res);
            res = new WordStatsProcessor().process(ips);
            outputHandler.addResult(fileName, res);
            res = new WordFrequencyProcessor().process(ips);
            outputHandler.addResult(fileName, res);
            // outputHandler.conclude();
        }
    }
}
