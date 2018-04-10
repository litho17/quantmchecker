package textcrunchr_1.com.cyberpointllc.stac.host;

import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;

import java.io.FileInputStream;
import java.io.InputStream;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(String[] args) throws Exception {
        while(true) {
            int INPUTINPUT = 10000;
            c16: INPUTINPUT -= 1;
            @Inv({"INPUTINPUT+<self>.results=+21+23+25+27+29-16"}) OutputHandler outputHandler = new WindowOutputHandler();
            String fileName = "";
            InputStream ips = new FileInputStream(fileName);
            TCResult res = new CharacterCountProcessor().process(ips);
            c21: outputHandler.addResult(fileName, res);
            res = new TextMeterProcessor().process(ips);
            c23: outputHandler.addResult(fileName, res);
            res = new EnigmaProcessor().process(ips);
            c25: outputHandler.addResult(fileName, res);
            res = new WordStatsProcessor().process(ips);
            c27: outputHandler.addResult(fileName, res);
            res = new WordFrequencyProcessor().process(ips);
            c29: outputHandler.addResult(fileName, res);
            // outputHandler.conclude();
        }
    }
}
