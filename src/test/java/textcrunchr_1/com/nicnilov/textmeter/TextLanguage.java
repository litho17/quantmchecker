package textcrunchr_1.com.nicnilov.textmeter;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;
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
import java.util.Locale;
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

    @Summary({"add"})
    public Ngram getNgram(NgramType ngramType, InputStream inputStream, NgramStorageStrategy ngramStorageStrategy, int sizeHint) throws IOException, LineFormatException {
        Ngram ngram = NgramBuilder.build(ngramType, inputStream, ngramStorageStrategy, sizeHint);
        ngrams.put(ngramType, ngram);
        return ngram;
    }

    public TextScore score(final String text) {
        @Inv("= (+ textScore it) (- c50 c48)") TextScore textScore = new  TextScore();
        Ngram ngram;
        @Inv("ngrams") Iterator<Map.Entry<NgramType, Ngram>> it = ngrams.entrySet().iterator();
        c48: while (it.hasNext()) {
            Map.Entry<NgramType, Ngram> entry = it.next();
            if ((ngram = entry.getValue()) != null) {
                c50: textScore.add(entry.getKey(), ngram.score(text));
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
