package textcrunchr_1.com.nicnilov.textmeter.ngrams;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.EnumMap;
import java.util.Map;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 27.10.13 at 23:03
 */
public class TextScore {

    public EnumMap<NgramType, Ngram.ScoreStats> ngramScores = new  EnumMap(NgramType.class);

    public EnumMap<NgramType, Ngram.ScoreStats> getNgramScores() {
        return ngramScores;
    }

    public String toString() {
        @Inv("ngramScores+<self>=+26-24") StringBuilder sb = new  StringBuilder();
        for (Map.Entry<NgramType, Ngram.ScoreStats> entry : ngramScores.entrySet()) {
            if (entry.getValue() != null) {
                toStringHelper(entry, sb);
            }
        }
        return sb.toString();
    }

    @Summary({"sb", "1"}) private void toStringHelper(Map.Entry<NgramType, Ngram.ScoreStats> entry, StringBuilder sb) {
        sb.append(String.format("%s: %.5f (min: %.5f total: %.0f found: %.0f)", entry.getKey(), entry.getValue().getScore(), entry.getValue().getMinScore(), entry.getValue().getNgramsTotal(), entry.getValue().getNgramsFound()));
    }
}
