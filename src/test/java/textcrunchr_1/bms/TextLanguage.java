package textcrunchr_1.bms;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.nicnilov.textmeter.NotInitializedException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.Ngram;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramBuilder;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.TextScore;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;

import java.io.IOException;
import java.io.InputStream;
import java.util.EnumMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 25.10.13 at 23:19
 */
public class TextLanguage {

    private EnumMap<NgramType, Ngram> ngrams = new  EnumMap(NgramType.class);

    private final String language;

    public TextLanguage(String language) {
        this.language = language;
    }

    protected Ngram getNgram(NgramType ngramType) {
        if (ngrams.containsKey(ngramType)) {
            return ngrams.get(ngramType);
        }
        throw new  NotInitializedException(String.format("Ngrams of type %s have not been loaded", ngramType));
    }

    public TextScore score(final String text) {
        @Inv("= (+ self.ngramScores it) (- (+ ngrams_init c54) c52)") TextScore textScore = new  TextScore();
        Ngram ngram;
        @Inv("ngrams") Iterator<Map.Entry<NgramType, Ngram>> it = ngrams.entrySet().iterator();
        c50: while (it.hasNext()) {
            Map.Entry<NgramType, Ngram> entry;
            c52: entry = it.next();
            if ((ngram = entry.getValue()) != null) {
                c54: textScore.add(entry.getKey(), ngram.score(text));
            }
        }
        return textScore;
    }

    public void releaseNgram(NgramType ngramType) {
        ngrams.remove(ngramType);
    }

    public void releaseAllNgrams() {
        ngrams.clear();
    }
}
