package textcrunchr_1.bms;

import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

public class TextFileHandler {

    List<Processor> processors = new  ArrayList<Processor>();

    public TextFileHandler() throws IOException {
        // todo - fill processors with list of processors
        @Inv("= self (+ c18 c19 c20 c25 c26)") List<Processor> processors = new  ArrayList<Processor>();
        c18: processors.add(new  CharacterCountProcessor());
        c19: processors.add(new  TextMeterProcessor());
        c20: processors.add(new  EnigmaProcessor());
        // Disabling SentenceStatsProcessor since there's a vulnerability in opennlp which is out
        // of scope for us at the moment. Leaving it commented in here because we might want
        // to bring it back someday.
        //processors.add(new SentenceStatsProcessor());
        c25: processors.add(new  WordStatsProcessor());
        c26: processors.add(new  WordFrequencyProcessor());
        this.processors = processors;
    }
}
