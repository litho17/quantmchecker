package textcrunchr_1.bms;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.Ngram;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;

import java.util.EnumMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Created as part of textmeter project
 * by Nic Nilov on 27.10.13 at 23:03
 */
public class TextScore {

    private @Input("1000") EnumMap<NgramType, Ngram.ScoreStats> ngramScores = new  EnumMap(NgramType.class);

    public EnumMap<NgramType, Ngram.ScoreStats> getNgramScores() {
        return ngramScores;
    }

    @Summary({"this.ngramScores", "1"})
    public void add(NgramType key, Ngram.ScoreStats value) {
        ngramScores.put(key, value);
    }

    @Override
    public String toString() {
        @Inv("= (+ self it) (- (+ ngramScores_init c25) c23)") StringBuilder sb = new  StringBuilder();
        @Inv("ngramScores") Iterator<Map.Entry<NgramType, Ngram.ScoreStats>> it = ngramScores.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<NgramType, Ngram.ScoreStats> entry;
            c23: entry = it.next();
            if (entry.getValue() != null) {
                c25: sb.append(String.format("%s: %.5f (min: %.5f total: %.0f found: %.0f)", entry.getKey(), entry.getValue().getScore(), entry.getValue().getMinScore(), entry.getValue().getNgramsTotal(), entry.getValue().getNgramsFound()));
            }
        }
        return sb.toString();
    }
}
