package com.cyberpointllc.stac.textcrunchr;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Locale;
import java.util.Scanner;
import org.apache.commons.io.IOUtils;
import com.cyberpointllc.stac.textcrunchr.Processor;
import com.nicnilov.textmeter.TextMeter;
import com.nicnilov.textmeter.TextLanguage;
import com.nicnilov.textmeter.TestUtils;
import com.nicnilov.textmeter.ngrams.NgramType;
import com.nicnilov.textmeter.ngrams.TextScore;
import com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;

class TextMeterProcessor extends Processor {

    private static final String NAME = "languageAnalysis";

    public TCResult process(InputStream inps) throws IOException {
        // read to string
        InputStreamReader is = new  InputStreamReader(inps);
        StringBuilder sb = new  StringBuilder();
        BufferedReader br = new  BufferedReader(is);
        String read = br.readLine();
        while (read != null) {
            //System.out.println(read);
            sb.append(read);
            read = br.readLine();
        }
        String theString = sb.toString();
        // set up textmeter
        TextMeter textMeter = new  TextMeter();
        textMeter.createTextLanguage("en");
        TextLanguage en = textMeter.get("en");
        long mark = System.currentTimeMillis();
        String message;
        try {
            en.getNgram(NgramType.UNIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_UNIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_UNIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.BIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_BIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_BIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.TRIGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_TRIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_TRIGRAMS_EXCNT);
            //        	en.getNgram(NgramType.QUADGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_QUADGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_QUADGRAMS_EXCNT);
            //        	en.getNgram(NgramType.QUINTGRAM, TestUtils.loadResource(this.getClass(), TestUtils.EN_QUINTGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_QUINTGRAMS_EXCNT);
            //        
            // score text
            TextScore textScore = en.score(theString.toUpperCase(Locale.ENGLISH));
            message = "en-based score for english text: " + textScore;
        } catch (LineFormatException lfe) {
            message = "Processing failed.";
            lfe.printStackTrace();
        }
        return new  TCResult("TextLanguage analysis:", message);
    }

    public String getName() {
        return NAME;
    }
}
