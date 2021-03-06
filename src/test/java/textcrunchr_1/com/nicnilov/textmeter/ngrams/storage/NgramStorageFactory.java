package textcrunchr_1.com.nicnilov.textmeter.ngrams.storage;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import textcrunchr_1.com.nicnilov.textmeter.NotImplementedException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 26.10.13 at 0:22
 */
public class NgramStorageFactory {

    public static NgramStorage get(NgramType ngramType, NgramStorageStrategy ngramStorageStrategy, int sizeHint) {
        @InvUnk("Unknown API") NgramStorage ngramStorage;
        switch (ngramStorageStrategy) {
            case HASHMAP: {
                ngramStorage = new HashMapStorage(ngramType, sizeHint);
                break;
            }
            case TREEMAP: {
                ngramStorage = new TreeMapStorage(ngramType);
                break;
            }
            //            }
            default: {
                throw new NotImplementedException();
            }
        }
        return ngramStorage;
    }
}
