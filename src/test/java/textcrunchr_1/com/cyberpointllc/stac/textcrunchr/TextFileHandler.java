package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

public class TextFileHandler {

    public List<Processor> processors = new ArrayList<Processor>();

    @Summary({"this.processors", "5"})
    public TextFileHandler() throws IOException {
        // todo - fill processors with list of processors
        processors.add(new CharacterCountProcessor());
        processors.add(new TextMeterProcessor());
        processors.add(new EnigmaProcessor());
        // Disabling SentenceStatsProcessor since there's a vulnerability in opennlp which is out
        // of scope for us at the moment. Leaving it commented in here because we might want
        // to bring it back someday.
        //processors.add(new SentenceStatsProcessor());
        processors.add(new WordStatsProcessor());
        processors.add(new WordFrequencyProcessor());
    }
}
