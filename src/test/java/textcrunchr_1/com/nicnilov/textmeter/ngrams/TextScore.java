package textcrunchr_1.com.nicnilov.textmeter.ngrams;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.EnumMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 27.10.13 at 23:03
 */
public class TextScore {

    private EnumMap<NgramType, Ngram.ScoreStats> ngramScores = new EnumMap(NgramType.class);

    public EnumMap<NgramType, Ngram.ScoreStats> getNgramScores() {
        return ngramScores;
    }

    @Summary({"this.ngramScores", "1"})
    public void add(NgramType key, Ngram.ScoreStats value) {
        ngramScores.put(key, value);
    }

    @Override
    public String toString() {
        @Input("") EnumMap<NgramType, Ngram.ScoreStats> ngramScores_ = this.ngramScores;
        @Inv("= (- sb it) (- c35 c33)") StringBuilder sb = new StringBuilder();
        @Iter("<= it ngramScores_") Iterator<Map.Entry<NgramType, Ngram.ScoreStats>> it = ngramScores_.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<NgramType, Ngram.ScoreStats> entry;
            c33: entry = it.next();
            if (entry.getValue() != null) {
                c35: toStringHelper(entry, sb);
            }
        }
        return sb.toString();
    }

    @Summary({"sb", "1"})
    private void toStringHelper(Map.Entry<NgramType, Ngram.ScoreStats> entry, StringBuilder sb) {
        sb.append(String.format("%s: %.5f (min: %.5f total: %.0f found: %.0f)", entry.getKey(), entry.getValue().getScore(), entry.getValue().getMinScore(), entry.getValue().getNgramsTotal(), entry.getValue().getNgramsFound()));
    }
}
