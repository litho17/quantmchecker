package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class TextFileHandler {

    @Inv("+<self>=+TextFileHandler17+TextFileHandler18+TextFileHandler19+TextFileHandler20+TextFileHandler21") List<Processor> processors;

    public TextFileHandler() throws IOException {
        processors = new ArrayList<Processor>();
        TextFileHandler17: processors.add(new CharacterCountProcessor());
        TextFileHandler18: processors.add(new TextMeterProcessor());
        TextFileHandler19: processors.add(new EnigmaProcessor());
        // Disabling SentenceStatsProcessor since there's a vulnerability in opennlp which is out
        // of scope for us at the moment. Leaving it commented in here because we might want
        // to bring it back someday.
        //processors.add(new SentenceStatsProcessor());
        TextFileHandler20: processors.add(new WordStatsProcessor());
        TextFileHandler21: processors.add(new WordFrequencyProcessor());
    }

    public void processFile(String filename, OutputHandler outph, String[] args) throws IOException {
        List<String> argsList = new ArrayList<String>(Arrays.asList(args));
        for (Processor processor : processors) {
            processFileHelper(outph, argsList, filename, processor);
        }
    }

    private void processFileHelper(OutputHandler outph, List<String> argsList, String filename, Processor processor) throws IOException {
        if (argsList.isEmpty() || argsList.contains(processor.getName())) {
            TCResult tcr = processor.process(new FileInputStream(filename));
            outph.addResult(filename, tcr);
        }
    }
}
