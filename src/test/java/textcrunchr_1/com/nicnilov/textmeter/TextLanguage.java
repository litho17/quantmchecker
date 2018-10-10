package textcrunchr_1.com.nicnilov.textmeter;

import plv.colorado.edu.quantmchecker.qual.*;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.Ngram;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramBuilder;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.TextScore;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorageFactory;
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

    public EnumMap<NgramType, Ngram> ngrams = new EnumMap(NgramType.class);

    private final String language;

    public TextLanguage(String language) {
        this.language = language;
    }

    protected Ngram getNgram(NgramType ngramType) {
        if (ngrams.containsKey(ngramType)) {
            return ngrams.get(ngramType);
        }
        throw new NotInitializedException(String.format("Ngrams of type %s have not been loaded", ngramType));
    }

    @Summary({"this.ngrams", "1"})
    public Ngram getNgram(NgramType ngramType, InputStream inputStream, NgramStorageStrategy ngramStorageStrategy, int sizeHint) throws IOException, LineFormatException {
        @InvUnk("Unknown API") Ngram ngram = new Ngram(ngramType, ngramStorageStrategy, sizeHint);
        ngram.ngramType = ngramType;
        ngram.ngramStorage = NgramStorageFactory.get(ngramType, ngramStorageStrategy, sizeHint);
        if (ngram.ngramStorage == null) {
            throw new NotInitializedException();
        }
        ngram.volume = ngram.ngramStorage.load(inputStream);
        if (ngram.volume != 0) {
            ngram.loadHelper();
        }
        ngram.calculateLogFrequences();
        ngrams.put(ngramType, ngram);
        return ngram;
    }

    public void releaseNgram(NgramType ngramType) {
        ngrams.remove(ngramType);
    }

    public void releaseAllNgrams() {
        ngrams.clear();
    }
}
