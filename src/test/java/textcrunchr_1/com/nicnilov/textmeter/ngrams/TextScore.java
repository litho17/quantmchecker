package textcrunchr_1.com.nicnilov.textmeter.ngrams;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorage;
import java.util.EnumMap;
import java.util.Map;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 27.10.13 at 23:03
 */
public class TextScore {

    private EnumMap<NgramType, Ngram.ScoreStats> ngramScores = new  EnumMap(NgramType.class);

    public EnumMap<NgramType, Ngram.ScoreStats> getNgramScores() {
        return ngramScores;
    }

    @Summary({"this.ngramScores", "1"})
    public void add(NgramType key, Ngram.ScoreStats value) {
        ngramScores.put(key, value);
    }

    @Override
    public String toString() {
        @Inv("+sb=-ngramScores.entrySet+c25-c23") StringBuilder sb = new  StringBuilder();
        c23: for (Map.Entry<NgramType, Ngram.ScoreStats> entry : ngramScores.entrySet()) {
            if (entry.getValue() != null) {
                c25: toStringHelper(entry, sb);
            }
        }
        return sb.toString();
    }

    @Summary({"sb", "1"})
    private void toStringHelper(Map.Entry<NgramType, Ngram.ScoreStats> entry, StringBuilder sb) {
        sb.append(String.format("%s: %.5f (min: %.5f total: %.0f found: %.0f)", entry.getKey(), entry.getValue().getScore(), entry.getValue().getMinScore(), entry.getValue().getNgramsTotal(), entry.getValue().getNgramsFound()));
    }
}
