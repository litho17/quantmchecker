package textcrunchr_1.com;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;

import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main() throws Exception {
        @Inv("= results (- (+ c28 c30 c32 c37) c38 c39 c40 c41)") List<TCResult> results = new ArrayList<>();
        String s;
        @Inv("= tcr1.results 0") TCResult tcr1;
        @Inv("= tcr2.results 0")TCResult tcr2;
        @Inv("= tcr3.results 0")TCResult tcr3;
        @Inv("= tcr4.results (- (+ c33 c34 c35 c36) c42 c43 c44 c45)")TCResult tcr4 = new TCResult("Word stats");
        while (true) {
            String filename = "";
            FileInputStream fis = new FileInputStream(filename);
            @Input("ufasdkfksfd") String[] s2;
            tcr1 = new CharacterCountProcessor().process(fis);
            c28: results.add(tcr1);
            tcr2 = new TextMeterProcessor().process(fis);
            c30: results.add(tcr2);
            tcr3 = new EnigmaProcessor().process(fis);
            c32: results.add(tcr3);
            c33: tcr4.addResult("Word count", "");
            c34: tcr4.addResult("Average word length", 0);
            c35: tcr4.addResult("Variance in word length", 0);
            c36: tcr4.addResult("Longest word: ", 0);
            c37: results.add(tcr4);
            c38: results.remove(tcr1);
            c39: results.remove(tcr2);
            c40: results.remove(tcr3);
            c41: results.remove(tcr4);
            c42: tcr4.removeResult();
            c43: tcr4.removeResult();
            c44: tcr4.removeResult();
            c45: tcr4.removeResult();
        }
    }
}
