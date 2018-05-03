package textcrunchr_1.com;

import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;

import java.io.FileInputStream;
import java.util.Queue;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public static void main(Queue<String> input) throws Exception {
        OutputHandler outph = new ConsoleOutputHandler();
        while (true) {
            String filename = input.poll();
            FileInputStream fis = new FileInputStream(filename);
            TCResult tcr;
            tcr = new CharacterCountProcessor().process(fis);
            outph.addResult(filename, tcr);
            tcr = new TextMeterProcessor().process(fis);
            outph.addResult(filename, tcr);
            tcr = new EnigmaProcessor().process(fis);
            outph.addResult(filename, tcr);
            tcr = new WordStatsProcessor().process(fis);
            outph.addResult(filename, tcr);
            tcr = new  WordFrequencyProcessor().process(fis);
            outph.addResult(filename, tcr);
        }
    }
}
