package textcrunchr_1.com;

import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;
import java.io.FileInputStream;
import java.util.Queue;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(Queue<String> input) throws Exception {
        @Inv("= (+ outph input input input input input) (- (+ c20 c22 c24 c26 c28) (+ c16 c16 c16 c16 c16))") OutputHandler outph = new ConsoleOutputHandler();
        while (true) {
            String filename;
            c16: filename = input.poll();
            FileInputStream fis = new FileInputStream(filename);
            TCResult tcr;
            tcr = new CharacterCountProcessor().process(fis);
            c20: outph.addResult(filename, tcr);
            tcr = new TextMeterProcessor().process(fis);
            c22: outph.addResult(filename, tcr);
            tcr = new EnigmaProcessor().process(fis);
            c24: outph.addResult(filename, tcr);
            tcr = new WordStatsProcessor().process(fis);
            c26: outph.addResult(filename, tcr);
            tcr = new  WordFrequencyProcessor().process(fis);
            c28: outph.addResult(filename, tcr);
        }
    }
}
