package textcrunchr_1.bms;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.ahancock.enigma.EnigmaFactory;
import textcrunchr_1.com.ahancock.enigma.EnigmaMachine;
import textcrunchr_1.com.cyberpointllc.stac.sort.DefaultComparator;
import textcrunchr_1.com.cyberpointllc.stac.sort.Sorter;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.ConsoleOutputHandler;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.OutputHandler;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.TCResult;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.TextMeterProcessor;
import textcrunchr_1.com.nicnilov.textmeter.TestUtils;
import textcrunchr_1.com.nicnilov.textmeter.TextLanguage;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.Ngram;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramBuilder;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.NgramType;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.TextScore;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.LineFormatException;
import textcrunchr_1.com.nicnilov.textmeter.ngrams.storage.NgramStorageStrategy;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.*;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public void main() throws Exception {
        @Input("100") int input = 0;
        @Inv("= (+ self.results input) (- (+ c53 c82 c103 c124 c174 input_init) c37)") OutputHandler outph = new ConsoleOutputHandler();
        while (true) {
            c37:
            input = input - 1;
            String filename = "test_file.txt";
            FileInputStream fis = new FileInputStream(filename);
            TCResult tcr;
            if (Math.random() > 0.8) {
                InputStreamReader isr = new InputStreamReader(fis);
                // count number of characters
                char buffer[] = new char[10000];
                int bytes_read = isr.read(buffer, 0, buffer.length);
                String value;
                if (bytes_read >= buffer.length) {
                    value = ">10,000 characters";
                } else {
                    value = bytes_read + " characters";
                }
                tcr = new TCResult("Character Count", value);
                c53:
                outph.addResult(filename, tcr);
            } else if (Math.random() > 0.6) {
                // read to string
                InputStreamReader is = new InputStreamReader(fis);
                @Inv("= (+ self br1) (- (+ inps_init c63) c64 c60)") StringBuilder sb = new StringBuilder();
                @Inv("inps") BufferedReader br1 = new BufferedReader(is);
                String read;
                c60:
                read = br1.readLine();
                while (read != null) {
                    //System.out.println(read);
                    c63:
                    sb.append(read);
                    c64:
                    read = br1.readLine();
                }
                String theString = sb.toString();
                @Inv("= self.ngrams c75") TextLanguage en = new TextLanguage("en");
                // @Inv("= self.textLanguages c70") TextMeter textMeter = new  TextMeter();
                // c70: textMeter.textLanguages.put("en", en);
                String message;
                try {
                    Ngram ngram;
                    ngram = NgramBuilder.build(NgramType.UNIGRAM, TestUtils.loadResource(new TextMeterProcessor().getClass(), TestUtils.EN_UNIGRAMS), NgramStorageStrategy.TREEMAP, TestUtils.EN_UNIGRAMS_EXCNT);
                    c75:
                    en.ngrams.put(NgramType.UNIGRAM, ngram);
                    TextScore textScore = en.score(theString.toUpperCase(Locale.ENGLISH));
                    message = "en-based score for english text: " + textScore;
                } catch (LineFormatException lfe) {
                    message = "Processing failed.";
                    lfe.printStackTrace();
                }
                tcr = new TCResult("TextLanguage analysis:", message);
                c82:
                outph.addResult(filename, tcr);
            } else if (Math.random() > 0.4) {
                // read to string
                InputStreamReader is = new InputStreamReader(fis);
                @Inv("= (+ self br2) (- (+ is_init c91) c89 c92)") StringBuilder sb = new StringBuilder();
                @Inv("is") BufferedReader br2 = new BufferedReader(is);
                String read;
                c89:
                read = br2.readLine();
                while (read != null) {
                    c91:
                    sb.append(read);
                    c92:
                    read = br2.readLine();
                }
                String theString = sb.toString().toUpperCase();
                // Construct the machine
                EnigmaMachine machine = EnigmaFactory.buildEnigmaMachine();
                // Set the rotors, encrypt the string and print the results
                machine.setRotors(5, 9, 14);
                String encodedString = machine.encodeLine(theString);
                String name = "Enigma transformation (5, 9, 14)";
                String value = encodedString;
                tcr = new TCResult(name, value);
                c103:
                outph.addResult(filename, tcr);
            } else if (Math.random() > 0.2) {
                InputStreamReader isr = new InputStreamReader(fis);
                // read to string
                @Inv("inps") BufferedReader br3 = new BufferedReader(new InputStreamReader(fis));
                @Inv("= (+ self br3) (- (+ inps_init c112) c110 c113)") StringBuilder sb = new StringBuilder();
                String read;
                c110:
                read = br3.readLine();
                while (read != null) {
                    c112:
                    sb.append(read);
                    c113:
                    read = br3.readLine();
                }
                String input_ = sb.toString();
                String regex = "[^\\p{Alnum}]+";
                String[] words = input_.split(regex);
                @Inv("= self.results (+ c119 c120 c121 c122)") TCResult result = new TCResult("Word stats");
                c119:
                result.addResult("Word count", words.length);
                c120:
                result.addResult("Average word length", meanLen(words));
                c121:
                result.addResult("Variance in word length", varLen(words));
                c122:
                result.addResult("Longest word: ", longest(words));
                tcr = result;
                c124:
                outph.addResult(filename, tcr);
            } else if (Math.random() > 0.1) {
                InputStreamReader isr = new InputStreamReader(fis);
                // count frequency of each word in input
                // read to string
                @Inv("inps") BufferedReader br = new BufferedReader(new InputStreamReader(fis));
                @Inv("= (+ self br) (- (+ inps_init c134) c132 c135)") StringBuilder sb = new StringBuilder();
                String read;
                c132:
                read = br.readLine();
                while (read != null) {
                    c134:
                    sb.append(read);
                    c135:
                    read = br.readLine();
                }
                String input_ = sb.toString();
                // get rid of apostrophes, so split won't
                input_.replace("'", "");
                // separates contractions into separate words
                // "\\s+;";
                String regex = "[^\\p{Alnum}]+";
                String[] words = input_.split(regex);
                // count the word frequencies
                @Inv("= (- self i) (- c158 c161 i_init)") List<WordCount> wordFreqs = new ArrayList<>();
                HashMap<String, WordCount> freqsCounter = new HashMap<>();
                @Input("100") int i = 0;
                for (; i < words.length; ) {
                    //making this case sensitive so that our carefully crafted hash collisions don't get obliterated
                    String w = words[i];
                    // increment current count for w
                    WordCount count = null;
                    if (freqsCounter.containsKey(w)) {
                        count = freqsCounter.get(w);
                    } else {
                        count = new WordCount(w, 0);
                        freqsCounter.put(w, count);
                        c158:
                        wordFreqs.add(count);
                    }
                    count.increment();
                    c161:
                    i = i + 1;
                }
                // sort results by most frequent
                Sorter<WordCount> sorter = new Sorter<>(new DefaultComparator<WordCount>());
                @Input("100") List<WordCount> sortedWCs = sorter.sort(wordFreqs);
                @Inv("= (+ self.results it) (- (+ sortedWCs_init c171) c170)") TCResult result = new TCResult("Word frequencies");
                @Inv("sortedWCs") Iterator<WordCount> it = sortedWCs.iterator();
                while (it.hasNext()) {
                    WordCount wc;
                    c170:
                    wc = it.next();
                    c171:
                    result.addResult(wc.getWord(), wc.getCount());
                }
                tcr = result;
                c174:
                outph.addResult(filename, tcr);
            } else {
                ;
            }
        }
    }

    /**
     * @param words
     * @return the longest word
     */
    private String longest(String[] words) {
        int maxLen = 0;
        String longestWord = "";
        for (String word : words) {
            int n = word.length();
            if (n > maxLen) {
                maxLen = n;
                longestWord = word;
            }
        }
        return longestWord;
    }

    /**
     * @param words
     * @return the mean word length
     */
    private double meanLen(String[] words) {
        double sum = 0;
        for (String s : words) {
            sum += s.length();
        }
        return sum / words.length;
    }

    /**
     * @param words
     * @return the variance in word length
     */
    private double varLen(String[] words) {
        double sum = 0;
        double sumSq = 0;
        for (String s : words) {
            int senLen = s.length();
            sum += senLen;
            sumSq += senLen * senLen;
        }
        int len = words.length;
        return sumSq / len - sum * sum / (len * len);
    }

    class WordCount implements Comparable<WordCount> {

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
            if (this.count == wc.getCount()) {
                return this.word.compareTo(wc.getWord());
            }
            // reverse natural order to get most frequent first
            return -1 * Integer.compare(this.count, wc.getCount());
        }
    }
}