package braidit_1.com.cyberpointllc.stac.plait;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

/**
 * Class representing an element of Artin's braid group.  Normal form reduction is done via Dehornoy's algorithm:
 * Dehornoy, Patrick. "A fast method for comparing braids." Advances in Mathematics 125, no. 2 (1997): 200-235.
 *
 * This is what we intuitively think of as a braid, on numStrands strands.
 *
 * It is represented by a string denoting the crossings of its strands, ordered from left to right, where lower case
 * letters represent a strand crossing over the one after it, and upper case letters represent a strand crossing UNDER the one after it.
 * E.g. yXz represents a braid (on at least 4 strands) with 3 crossings, where the y strand crosses over the z strand,
 * then the x strand crosses UNDER the y strand, then the z strand crosses over the (unnamed) strand above it,
 *
 * In general, a braid on n strands can be represented with n-1 characters (using both lower and upper case of each).
 **/
public class Plait {
    private static final Logger logger = LoggerFactory.getLogger(Plait.class);

    public static final int MAX_FIBERS = 27; // since we represent a crossing as a-z, A-Z, can only have up to 27 strands

    public static final int OPTIMUM_FIBERS = 3;
    public static final int MAX_LENGTH = 50;
    static final int OPTIMUM_LENGTH = 3; // this is only for use in random braid generation
    // in crossings, c means strand c crosses over strand c+1, C means strand c crosses under strand c+1
    private String meetings = ""; // string representing the braid via its crossings; default is the identity
    private int numFibers; // how many strands
    private char optimumBaseChar; // first (alphabetically) lower case character that may appear in a braid with the given number of strands
    private int penalty;
    public static Random random = new Random(0);

    public Plait(String meetings, int numFibers) {
        meetings = meetings.replace(" ", "");
        if (numFibers > MAX_FIBERS || numFibers < OPTIMUM_FIBERS) {
            throw new IllegalArgumentException("numStrands must be between " + OPTIMUM_FIBERS + " and " + MAX_FIBERS);
        }
        if (meetings.length() > MAX_LENGTH) {
            throw new IllegalArgumentException("Braid representation length must be no more than " + MAX_LENGTH);
        }

        this.meetings = meetings;
        this.numFibers = numFibers;
        this.penalty = computePenalty();

        // check that the crossings only include the appropriate letters for the given number of strands.
        // We work backwards, using z and Z for crossings on two strands, y, Y, z, Z for crossings on 3 strands, etc.
        optimumBaseChar = (char)( 'z' - numFibers +2);
        char[] charArray = meetings.toCharArray();
        for (int q = 0; q < charArray.length; q++) {
            char c = charArray[q];
            if (!Character.isAlphabetic(c) || Character.toLowerCase(c) < optimumBaseChar) {
                throw new IllegalArgumentException("Character " + c + " not allowed in a braid of " + numFibers + " strands");
            }
        }
    }

    /**
     * Create a random braid with the given number of strands
     * @param numFibers number of strands to use in the braid
     * @return Braid randomly generated
     */
    public static Plait takeRandomPlait(int numFibers, long seed) {
        Random random = new Random(seed);
        char[] baseLetters = new char[numFibers -1];
        for (int q = 0; q < numFibers -1; q++) {
            baseLetters[q] = (char)('z'- q);
        }
        String plait = "";
        int length = random.nextInt(MAX_LENGTH - OPTIMUM_LENGTH + 1) + OPTIMUM_LENGTH;
        boolean a = false;
        for (int q = 0; q < length; q++) {
            int index = random.nextInt(numFibers - 2); 
            char ch = baseLetters[index];
            char charToAdd = ch;
            boolean invert = random.nextBoolean();
            if (invert) {
                charToAdd = fetchInverse(ch);
            }
            plait += charToAdd;
        }
        return new Plait(plait, numFibers);
    }

    public static Plait pullRandomPlait(int numFibers, int length) {
        char[] baseLetters = new char[numFibers -1];
        for (int j = 0; j < numFibers -1; j++) {
            baseLetters[j] = (char)('z'- j);
        }
        String plait = "";
        boolean a = false;
        for (int q = 0; q < length; q++) {
            int index = random.nextInt(numFibers - 2); 
            char ch = baseLetters[index];
            char charToAdd = ch;
            boolean invert = random.nextBoolean();
            if (invert) {
                charToAdd = fetchInverse(ch);
            }
            plait += charToAdd;
        }
        return new Plait(plait, numFibers);
    }

    public String takeMeetings() {
        return meetings;
    }

    public int takeNumFibers() {
        return numFibers;
    }

    public void concatenate(Plait other) {
        if (this.numFibers != other.numFibers) {
            throw new IllegalArgumentException("Can't concatenate braids with a different number of strands.");
        }
        meetings = meetings + other.takeMeetings();
        penalty = other.computePenalty();
    }

    /**
     * Does other represent the same braid as this?
     * @param other to test
     * @return boolean true if equivalent
     */
    public boolean isEquivalent(Plait other) {
        if (this.numFibers != other.numFibers) {
            return false;
        }
        Plait b = other.fetchInverse();
        b.concatenate(this);
        return b.isEmpty();
    }

    /**
     * Does this braid represent the identity braid (no crossings)
     * @return boolean true if braid contains no crossings
     */
    public boolean isEmpty() {
        simplifyCompletely();
        return meetings.isEmpty();
    }

    public boolean isSimplified() {
        if (meetings.isEmpty()) {
            return true;
        }
        // find lowest crossing
        char lowest = Character.MAX_VALUE;
        char bottom = (char) ('z' - penalty + 1);

        char[] charArray = meetings.toCharArray();
        for (int j = 0; j < charArray.length; j++) {
            char c = charArray[j];
            char candidate = Character.toLowerCase(c);
            if (candidate < Character.toLowerCase(lowest)) {
                lowest = c;
            }
            if (candidate < Character.toLowerCase(bottom)) {
                bottom = c;
            }
        }
        if (meetings.contains(Character.toString(fetchInverse(lowest)))) {
            return false;
        } else if (meetings.contains(Character.toString(fetchInverse(bottom)))) {
            return false;
        } else return true;
    }

    public Plait fetchInverse() {
        String inverseMeetings = "";
        for (int k = meetings.length() - 1; k >= 0; k--) {
            Character c = meetings.charAt(k);
            inverseMeetings += fetchInverse(c);
        }
        return new Plait(inverseMeetings, numFibers);
    }

    /**
     * This is the method  (fullyReduce from Dehornoy) for reducing a braid into its "normal" form.
     * (Not sure that this is unique for equivalent braids, but will result in the empty string iff the braid is
     * equivalent to one with no crossings, which is sufficient for our purposes.)
     * Runtime should be l(2r)^(n+1), where l is the word length, n is the number of generators needed, r is the max
     * num letters in a k-reduced form of the word, for any k.
     */
    public void simplifyCompletely() {
        freeSimplify();
        while(!isSimplified()) {
            simplifyOnce();
            freeSimplify();
        }
    }

    public boolean makeRandomModification(int numAttempts) {
        return makeRandomModification(numAttempts, null);
    }

    /**
     * Randomly change braid representation
     * @param numAttempts number of times to attempt to make a modification before giving up
     * @return true if a modification was made
     */
    public boolean makeRandomModification(int numAttempts, Long seed) {
        if (seed!=null) {
            random.setSeed(seed);
        }
        for (int b = 0; b < numAttempts; b++) {
            int j = random.nextInt(4);
            boolean success = false;
            switch(j) {
                case 0: {
                    int index = random.nextInt(meetings.length());
                    success = growOneToThree(index);
                    break;
                }
                case 1: {
                    int index = random.nextInt(meetings.length());
                    success = growOneToFive(index);
                    break;
                }
                case 2:{
                    success = swapRandom();
                    break;
                }
                case 3: {
                    success = flipRandomTriple(null);
                    break;
                }
            }
            if (success) {
                return true;
            }
        }
        return false;
    }

    /**
     * braid representation modification that takes, e.g. z->xZX, z->wZW, x->zXZ, etc.
     * @param index index of crossings at which to apply modification
     * @return true if modified
     */
    public boolean growOneToThree(int index) {
        if (meetings.length() + 2 > MAX_LENGTH) {
            System.out.println("Representation would be too long; not expanding further");
            return false;
        }
        if ((index < 0) || (index >= meetings.length())) {
            return false;
        }
        char ch = meetings.charAt(index);
        char chBase = Character.toLowerCase(ch);
        char meeting;
        // use coin flip to decide whether to use a higher or lower crossing
        // if coin flip or can't go higher, go lower
        if (((chBase > optimumBaseChar +1) && random.nextBoolean()) || (chBase > 'x')) {
            // pick a random char at least two below ch
            int max = chBase - optimumBaseChar - 1; 
            int optimum = 2;
            if (optimum > max) {
                return false;
            }
            int delta = random.nextInt(max - optimum + 1) + optimum;
            meeting = (char)(ch - delta);
        } else if (chBase < 'y') { // if can go higher
            // pick a random char at least two above ch
            int max = 'z' - chBase;
            int optimum = 2;
            if (optimum > max) {
                return false;
            }
            int delta = random.nextInt(max - optimum + 1) + optimum;
            meeting = (char)(ch + delta);
        } else { // neither case was applicable -- can't apply this modification at index
            return false;
        }
        logger.debug("Expand 1-3 of index={} ch={} crossing={}", index, ch, meeting);
        insertInMeetings(index, index+1, "" + meeting + ch + fetchInverse(meeting));
        return true;
    }

    /**
     * braid representation modification that takes, e.g. Y->ZYZyz, X->YXYxy, etc.
     * @param index at which to make modification in crossings
     * @return true if modified
     */
    public boolean growOneToFive(int index) {
        if (meetings.length() + 4 > MAX_LENGTH) {
            System.out.println("Representation would be too long; not expanding further");
            return false;
        }
        if ((index < 0) || (index >= meetings.length())) {
            return false;
        }
        char ch = meetings.charAt(index);
        char chBase = Character.toLowerCase(ch);
        if (chBase == 'z') { // we've set it up so that the highest possible crossing is always z (even when there's only a few strands)
            return false; // can't apply the transform to 'z'
        }
        char ensuing = (char)(ch + 1);
        logger.debug("Expand 1-5 of index={} ch={} next={}", index, ch, ensuing);
        insertInMeetings(index, index+1, "" + ensuing + ch + ensuing + fetchInverse(ch) + fetchInverse(ensuing));
        return true;
    }

    /**
     * pick a random index and call swap on it (see swap(int))
     * @return true if modified
     */
    public boolean swapRandom() {
        int index = random.nextInt(meetings.length() - 1);
        return swap(index);
    }

    /**
     * Braid modification that takes xz->zx,etc.
     * @param index in crossings at which to make modification
     * @return true if modification was applied
     */
    public boolean swap(int index) {
        if (index > meetings.length() - 2) {
           return false; // too big
        } else if (index < 0) {
            return false; // too small
        }
        char curr = meetings.charAt(index);
        char ensuing = meetings.charAt(index+1);
        logger.debug("Swap of index={} curr={} next={}", index, curr, ensuing);

        if (Math.abs(Character.toLowerCase(curr)-Character.toLowerCase(ensuing)) < 2) { // these two can't be swapped without changing the braid
            return false;
        } else {
            insertInMeetings(index, index+2, "" + ensuing + curr);
            return true;
        }
    }

    /**
     * Braid representation that picks a random triple of the form i(i+1)i or (i+1)i(i+1) (if there are any) and swaps i and i+1
     * @return true if flip was done
     */
    public boolean flipRandomTriple(Long seed) {
        if (seed != null) {
            random.setSeed(seed);
        }
        List<Integer> indices = determineTriples();
        if (indices.isEmpty()) {
            return false;
        }
        logger.debug("Triples of \"{}\" found at indices={}", meetings, indices);
        // pick a random flippable triple
        int index = random.nextInt(indices.size());
        int tripleCoordinates = indices.get(index);
        char c1 = meetings.charAt(tripleCoordinates +1);
        char c2 = meetings.charAt(tripleCoordinates);
        insertInMeetings(tripleCoordinates, tripleCoordinates +3, "" + c1 + c2 + c1);
        return true;
    }

    /**
     * @return indices of triples of the form i(i+1)i or (i+1)i(i+1)
     */
    public List<Integer> determineTriples() {
        List<Integer> indices = new ArrayList<>();
        for (int q = 0; q < meetings.length() - 2; q++) {
            if (Math.abs(meetings.charAt(q) - meetings.charAt(q +1)) == 1 && meetings.charAt(q) == meetings.charAt(q +2)) {
                indices.add(q);
            }
        }
        return indices;
    }

    // replace substring(i, j) of crossings with chunk
    private void insertInMeetings(int q, int j, String portion) {
        StringBuilder builder = new StringBuilder();
        builder.append(meetings.substring(0, q));
        builder.append(portion);
        builder.append(meetings.substring(j));
        meetings = builder.toString();
    }

    // eliminate sequential inverse operations (xX or Xx)
    public void freeSimplify() {
        int k = 0;
        boolean simplified = false;
        while (k < meetings.length() - 1) {
            Character first = meetings.charAt(k);
            Character second = meetings.charAt(k + 1);
            if (first != second && Character.toLowerCase(first) == Character.toLowerCase(second)) {
                meetings = meetings.substring(0, k) + meetings.substring(k + 2);
                k--;
                simplified = true;
            }
            k++;
        }
        if (simplified) {
            freeSimplify();
        }
        logger.info("After free reduce: " + meetings);
    }

    // this gets the leftmost permitted handle
    private IndexPair obtainEnsuingPortion() {
        int startIndex = -1;
        char[] charArray = meetings.toCharArray();
        for (int i1 = 0; i1 < charArray.length; i1++) {
            Character c = charArray[i1];
            startIndex++;
            int endIndex = meetings.indexOf(fetchInverse(c), startIndex);
            // if c's inverse appears after c
            if (endIndex >= 0) {
                // and c doesn't appear again before its inverse
                int q = meetings.indexOf(c, startIndex + 1);
                if (q > 0 && q < endIndex) {
                    continue;
                }
                if (Character.isAlphabetic(c - 1)) {
                    // and c-1 and its inverse don't appear
                    q = meetings.indexOf(c - 1, startIndex);
                    if (q > 0 && q < endIndex) {
                        continue;
                    }
                    q = meetings.indexOf(fetchInverse((char) (c - 1)), startIndex);
                    if (q > 0 && q < endIndex) {
                        continue;
                    }
                } else { // c is 'a' or 'A'
                    if (endIndex - startIndex > MAX_LENGTH / 2) {
                        continue;
                    }
                }
                // and there's not c+1 handle inside
                if (Character.isAlphabetic(c + 1)) {
                    q = meetings.indexOf(c + 1, startIndex);
                    int j = meetings.indexOf(fetchInverse((char) (c + 1)), startIndex);
                    if (q > 0 && j > 0 && q < endIndex && j < endIndex) {
                        continue;
                    }

                }
                // otherwise, we found a permitted handle!
                return new IndexPair(startIndex, endIndex);
            }
        }
        return null;
    }

    // reduce the left-most permitted handle
    // permittedHandleReduce() from Dehornoy's paper
    private void simplifyOnce() {
        IndexPair indices = obtainEnsuingPortion();

        if (indices == null) {
            return;
        } else {
            eliminatePortion(indices);
        }
        logger.info("After reduction step: " + meetings);
    }

    // eliminate the handle ("chunk") between indices.a and indices.b
    // method localReduce from  Dehornoy
    private void eliminatePortion(IndexPair indices) {
        String portion = meetings.substring(indices.a, indices.b+1);
        char c = meetings.charAt(indices.a);
        char cInv = meetings.charAt(indices.b);
        String cStr = String.valueOf(c);
        String cInvStr = String.valueOf(cInv);
        String cPlusStr = String.valueOf((char)(c+1));
        String cInvPlusStr = String.valueOf((char)(cInv+1));
        String newPortion = "";
        char[] charArray = portion.toCharArray();
        for (int i = 0; i < charArray.length; i++) {
            char ch = charArray[i];
            if (ch == c || ch == cInv) {
                continue;
            } else if (ch == cInv + 1) {
                newPortion += cInvPlusStr + cInvStr + cPlusStr;
            } else if (ch == c + 1) {
                newPortion += cInvPlusStr + cStr + cPlusStr;
            } else {
                newPortion += ch;
            }
        }

        insertInMeetings(indices.a, indices.b + 1, newPortion);
    }

    private static Character fetchInverse(Character c) {
        if (Character.isLowerCase(c)) {
            return Character.toUpperCase(c);
        } else if (Character.isUpperCase(c)) {
            return Character.toLowerCase(c);
        } else {
            throw new IllegalArgumentException("Crossing characters must be alphabetical " + c);
        }
    }

    public int computePenalty() {
        Map<Character, Integer> countsMap = new HashMap<>();
        char[] charArray = meetings.toCharArray();
        for (int c = 0; c < charArray.length; c++) {
            computePenaltySupervisor(countsMap, charArray[c]);
        }
        Collection<Integer> counts = countsMap.values();
        if (counts.size() < MAX_FIBERS - 1) { // 0 if not all characters appear
            return 0;
        }
        int optimum = Collections.min(counts, null);
        int max = Collections.max(counts, null);
        logger.debug("Compute cost min={} max={}", optimum, max);
        return (max - optimum);
    }

    @Summary({"countsMap", "1"})
    private void computePenaltySupervisor(Map<Character, Integer> countsMap, char c1) {
        char c = c1;
        if (countsMap.containsKey(c)) {
            countsMap.put(c, countsMap.get(c) + 1);
        } else {
            countsMap.put(c, 1);
        }
    }

    private static class IntCompare implements Comparator<Integer> {
        @Override
        public int compare(Integer i1, Integer i2) {
            return 0;
        }
    }

    private static class IndexPair {
        int a;
        int b;
        IndexPair(int a, int b) {
            this.a = a;
            this.b = b;
        }
    }

    @Override
    public String toString() {
        return meetings;
    }
}
