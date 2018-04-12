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
            Driver16: INPUTINPUT -= 1;
            OutputHandler outputHandler;
            outputHandler = new WindowOutputHandler();
            String fileName = "";
            InputStream ips = new FileInputStream(fileName);
            TCResult res = new CharacterCountProcessor().process(ips);
            Driver21: outputHandler.addResult(fileName, res);
            res = new TextMeterProcessor().process(ips);
            Driver23: outputHandler.addResult(fileName, res);
            res = new EnigmaProcessor().process(ips);
            Driver25: outputHandler.addResult(fileName, res);
            res = new WordStatsProcessor().process(ips);
            Driver27: outputHandler.addResult(fileName, res);
            res = new WordFrequencyProcessor().process(ips);
            Driver29: outputHandler.addResult(fileName, res);
            // outputHandler.conclude();
        }
    }
}
