package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class TextFileHandler {

    @Inv("+processors=+c18+c19+c20+c25+c26") List<Processor> processors;

    public TextFileHandler() throws IOException {
        // todo - fill processors with list of processors
        processors = new  ArrayList<Processor>();
        c18: processors.add(new  CharacterCountProcessor());
        c19: processors.add(new  TextMeterProcessor());
        c20: processors.add(new  EnigmaProcessor());
        // Disabling SentenceStatsProcessor since there's a vulnerability in opennlp which is out
        // of scope for us at the moment. Leaving it commented in here because we might want
        // to bring it back someday.
        //processors.add(new SentenceStatsProcessor());
        c25: processors.add(new  WordStatsProcessor());
        c26: processors.add(new  WordFrequencyProcessor());
    }

    public void processFile(String filename, OutputHandler outph, String[] args) throws IOException {
        List<String> argsList = new  ArrayList<String>(Arrays.asList(args));
        for (Processor processor : processors) {
            if (argsList.isEmpty() || argsList.contains(processor.getName())) {
                TCResult tcr = processor.process(new  FileInputStream(filename));
                outph.addResult(filename, tcr);
            }
        }
    }
}
