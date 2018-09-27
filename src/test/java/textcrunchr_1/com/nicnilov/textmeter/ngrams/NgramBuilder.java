package textcrunchr_1.com.nicnilov.textmeter.ngrams;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;

import java.io.IOException;
import java.io.InputStream;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 26.10.13 at 0:12
 */
public class NgramBuilder {

    public static Ngram build(NgramType ngramType, InputStream inputStream, NgramStorageStrategy ngramStorageStrategy, int sizeHint) throws IOException, LineFormatException {
        @InvUnk("Arbitrary update") Ngram ngram = new Ngram(ngramType, ngramStorageStrategy, sizeHint);
        ngram.load(inputStream);
        return ngram;
    }
}
