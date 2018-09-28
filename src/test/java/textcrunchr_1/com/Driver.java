package textcrunchr_1.com;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;
import java.io.FileInputStream;
import java.util.*;

import plv.colorado.edu.quantmchecker.qual.Input;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(@Input("(and (<= i input) (<= input 100))") List<Object> input) throws Exception {
        int i = 0;
        @Inv("= (- results i) (- (+ c23 c25 c27 c29 c31) c21)") List<TCResult> results = new ArrayList<>();
        String s;
        while (true) {
            c21: i = i + 1;
            String filename = "";
            FileInputStream fis = new FileInputStream(filename);
            @InvUnk("Method return list") TCResult tcr;
            if (Math.random() > 0.8) {
                tcr = new CharacterCountProcessor().process(fis);
                c23: results.add(tcr);
            } else if (Math.random() > 0.6) {
                tcr = new TextMeterProcessor().process(fis);
                c25: results.add(tcr);
            } else if (Math.random() > 0.4) {
                tcr = new EnigmaProcessor().process(fis);
                c27: results.add(tcr);
            } else if (Math.random() > 0.2) {
                tcr = new WordStatsProcessor().process(fis);
                c29: results.add(tcr);
            } else if (Math.random() > 0.1) {
                tcr = new WordFrequencyProcessor().process(fis);
                c31: results.add(tcr);
            } else {
                ;
            }
        }
    }
}
