package com.nicnilov.textmeter.ngrams;

import com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;
import plv.colorado.edu.quantmchecker.qual.ListInv;

import java.io.IOException;
import java.io.InputStream;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 26.10.13 at 0:12
 */
public class NgramBuilder {

    public static Ngram build(NgramType ngramType, InputStream inputStream, NgramStorageStrategy ngramStorageStrategy, int sizeHint) throws IOException, LineFormatException {
        @ListInv("<self>.ngramStorage.storage+rem(inputStream)=NgramStorage.c48-NgramStorage.c42") Ngram ngram = new Ngram(ngramType, ngramStorageStrategy, sizeHint);
        ngram.load(inputStream);
        return ngram;
    }
}
