package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import textcrunchr_1.com.nicnilov.textmeter.TestUtils;
import textcrunchr_1.com.nicnilov.textmeter.TextLanguage;
import textcrunchr_1.com.nicnilov.textmeter.TextMeter;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.TextScore;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Locale;

public class TextMeterProcessor extends Processor {

    private static final String NAME = "languageAnalysis";

    public TCResult process(InputStream inps) throws IOException {
        // read to string
        InputStreamReader is = new InputStreamReader(inps);
        StringBuilder sb = new StringBuilder();
        BufferedReader br = new BufferedReader(is);
        String read;
        read = br.readLine();
        while (read != null) {
            //System.out.println(read);
            sb.append(read);
            read = br.readLine();
        }
        String theString = sb.toString();
        // set up textmeter
        TextMeter textMeter = new TextMeter();
        textMeter.createTextLanguage("en");
        @InvUnk("Method return list") TextLanguage en = textMeter.get("en");
        long mark = System.currentTimeMillis();
        String message;
        try {
            c42: en.getNgram(NgramType.UNIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_UNIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_UNIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.BIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_BIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_BIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.TRIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_TRIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_TRIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.QUADGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_QUADGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_QUADGRAMS_EXCNT);
            //        	en.getNgram(NgramType.QUINTGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_QUINTGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_QUINTGRAMS_EXCNT);
            //        
            // score text
            @InvUnk("Method return list") TextScore textScore = en.score(theString.toUpperCase(Locale.ENGLISH));
            message = "en-based score for english text: " + textScore;
        } catch (LineFormatException lfe) {
            message = "Processing failed.";
            lfe.printStackTrace();
        }
        return new TCResult("TextLanguage analysis:", message);
    }

    public String getName() {
        return NAME;
    }
}
