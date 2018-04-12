package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.cyberpointllc.stac.sort.DefaultComparator;
import textcrunchr_1.com.cyberpointllc.stac.sort.Sorter;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
// import com.cyberpointllc.stac.hashmap.HashMap;

public class WordFrequencyProcessor extends Processor {

    private static final String NAME = "wordFreqs";

    public TCResult process(InputStream inps) throws IOException {
        InputStreamReader isr = new  InputStreamReader(inps);
        // count frequency of each word in input
        String input = readInput(inps);
        String words[] = tokenize(input);
        // count the word frequencies
        List<WordCount> wordFreqs = countWords(words);
        // sort results by most frequent
        Sorter<WordCount> sorter = new  Sorter<WordCount>(new  DefaultComparator<WordCount>());
        List<WordCount> sortedWCs = sorter.sort(wordFreqs);
        TCResult result = new  TCResult("Word frequencies");
        WordFrequencyProcessor31: for (WordCount wc : sortedWCs) {
            WordFrequencyProcessor32: result.addResult(wc.getWord(), wc.getCount());
        }
        return result;
    }

    public String getName() {
        return NAME;
    }

    /**
     *
     * @param words
     * @return List containing number of appearances of each word (words are
     *         lower-cased for counting purposes).
     */
    private List<WordCount> countWords(String[] words) {
        @Inv({"words+<self>=+WordFrequencyProcessor60-WordFrequencyProcessor50"}) List<WordCount> freqs = new  ArrayList<WordCount>();
        @Inv("words+<self>=+WordFrequencyProcessor59-WordFrequencyProcessor50") HashMap<String, WordCount> freqsCounter = new HashMap<String, WordCount>();
        WordFrequencyProcessor50: for (String word : words) {
            //making this case sensitive so that our carefully crafted hash collisions don't get obliterated
            String w = word;
            // increment current count for w
            WordCount count = null;
            if (freqsCounter.containsKey(w)) {
                count = freqsCounter.get(w);
            } else {
                count = new  WordCount(w, 0);
                WordFrequencyProcessor59: freqsCounter.put(w, count);
                WordFrequencyProcessor60: freqs.add(count);
            }
            count.increment();
        }
        // freqs = new ArrayList<WordCount>();
        return freqs;
    }

    /**
     *
     * @param input
     * @return array of words in input
     */
    private String[] tokenize(String input) {
        // get rid of apostrophes, so split won't
        input.replace("'", "");
        // separates contractions into separate words
        // "\\s+;";
        String regex = "[^\\p{Alnum}]+";
        String[] words = input.split(regex);
        return words;
    }

    /*
     * read the input into a String
     */
    private String readInput(InputStream inps) throws IOException {
        // read to string
        BufferedReader br = new  BufferedReader(new  InputStreamReader(inps));
        @Inv("br+<self>=+WordFrequencyProcessor92-WordFrequencyProcessor90-WordFrequencyProcessor91") StringBuilder sb = new  StringBuilder();
        String read;
        WordFrequencyProcessor90: read = br.readLine();
        while (read != null) {
            WordFrequencyProcessor92: sb.append(read);
            WordFrequencyProcessor91: read = br.readLine();
        }
        return sb.toString();
    }

    /**
     * Comparable object that we can sort to keep track of which words had
     * higher counts
     */
    private class WordCount implements Comparable<WordCount> {

        private String word;

        private int count;

        public WordCount(String w, int c) {
            this.word = w;
            this.count = c;
        }

        public int getCount() {
            return count;
        }

        public void increment() {
            count++;
        }

        public String getWord() {
            return word;
        }

        public String toString() {
            return word + ": " + count;
        }

        public int compareTo(WordCount wc) {
            WordCountHelper0 conditionObj0 = new  WordCountHelper0(0);
            if (Integer.compare(this.count, wc.getCount()) == conditionObj0.getValue()) {
                return this.word.compareTo(wc.getWord());
            }
            // reverse natural order to get most frequent first
            return -1 * Integer.compare(this.count, wc.getCount());
        }

        public class WordCountHelper0 {

            public WordCountHelper0(int conditionRHS) {
                this.conditionRHS = conditionRHS;
            }

            private int conditionRHS;

            public int getValue() {
                return conditionRHS;
            }
        }
    }
}
