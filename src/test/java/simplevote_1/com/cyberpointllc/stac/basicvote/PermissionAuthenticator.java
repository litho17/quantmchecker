package simplevote_1.com.cyberpointllc.stac.basicvote;

import simplevote_1.com.cyberpointllc.stac.algorithm.FunkyFunction;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;

public class PermissionAuthenticator {
    protected static final int[] interpreter = {3, 1, 11, 5, 2, 9, 10, 7, 8, 0, 4, 6};
    protected static final int DIGITS_OF_VAL = 6;
    protected static final int DIGITS_OF_N = 6;
    protected static final int LENGTH = DIGITS_OF_VAL + DIGITS_OF_N;
    protected static final double SEED = .375;
    protected static final int GAP = 7; // we only accept keys that have n a multiple of GAP

    protected static int MAX_N = 995;

    private final DirectVoteService directVoteService;
    private final FunkyFunction map;

    public PermissionAuthenticator(DirectVoteService directVoteService){
        this.directVoteService = directVoteService;

        map = new FunkyFunction();
    }

    public boolean confirm(String string) {
        if (string == null) {
            return false;
        }

        string = string.trim();

        if (string.length() != LENGTH) {
            return false;
        }

        // unshuffle and replace special characters with ints
        char[] chars = new char[LENGTH];
        for (int i = 0; i < LENGTH; i++) {
            chars[i] = string.charAt(interpreter[i]);
            // submitted nstr shouldn't contain 7, 6, or 3 -- those were replaced with letters
            if (i>=6 && (chars[i] == '3' || chars[i] == '6' || chars[i] == '7')){
               return false;
            }
            // now replace the letters with those digits
            if (chars[i] == 'A') {
                chars[i] = '7';
            } else if (chars[i] == 'C') {
                chars[i] = '6';
            } else if (chars[i] == 'E') {
                chars[i] = '3';
            }
        }

        boolean isCount = true;
        for (int i = 0; i < LENGTH; i++) {
            isCount &= Character.isDigit(chars[i]);
        }

        if (!isCount) {
            return false;
        }

        String decoded = new String(chars);

        // split parts
        String kStr = decoded.substring(0, DIGITS_OF_VAL);
        String nStr = decoded.substring(DIGITS_OF_VAL);

        int n = Integer.parseInt(nStr);

        if (!isInBounds(n)){
            return false;
        }

        // verify
        return confirmEssence(kStr, n) && confirmForm(kStr, n);
        }

    private boolean isInBounds(int n){
        if (n >= MAX_N) {
            return new PermissionAuthenticatorUtility(n).invoke();
        }
        if (n < 0) {
            return false;
        }
        return true;
    }

    private boolean confirmForm(String str, int n) {

        return n % GAP == 0;
    }

    private boolean confirmEssence(String str, int n) {
        return confirmEssence(str, n, -n, false);
    }

    private boolean confirmEssence(String str, int n, int p, boolean lastReply) {
        if (!directVoteService.isVotingActivated()) {
            return false;
        }

        boolean reply = lastReply;

        double val= map.funkyFunction(p).doubleValue();
        if (matches(val, str)) {
            reply = true;
        } else {
            if (lastReply) {
                reply = false;
            }
        }

        return assessRange(str, n, p, reply);
    }

    private boolean assessRange(String str, int n, int a, boolean reply) {
        if (a < n) {
            a++;
            reply = confirmEssence(str, n, a, reply);
        }
        return reply;
    }
    private boolean matches(double val, String str) {
        BigInteger digits = new BigInteger(takeKSigDigits(val, DIGITS_OF_VAL).toString());
        String digitsStr = "";
        for (char c : getChars(digits)){
            digitsStr += c;
        }

        boolean areEqual = true;

        if (digitsStr.length() != str.length()) {
            areEqual = false;
        }

        for (int i = 0; i < digitsStr.length() && i < str.length(); i++) {
            if (str.charAt(i) != digitsStr.charAt(i)) {
                areEqual = false;
            }
        }
        return areEqual;
    }

    private char[] getChars(BigInteger bigInt){
        return bigInt.toString().toCharArray();
    }

    // return an int with the k most significant digits of x
    protected BigInteger takeKSigDigits(double x, int k) {
        MathContext mc = new MathContext(k);
        BigDecimal sigEssence = new BigDecimal(x).round(mc);
        BigInteger unscaled = sigEssence.unscaledValue();
        return unscaled;
    }

    private class PermissionAuthenticatorUtility {
        private int n;

        public PermissionAuthenticatorUtility(int n) {
            this.n = n;
        }

        public boolean invoke() {
            if (n==MAX_N){
                MAX_N = MAX_N + GAP;
            }
            return false;
        }
    }
}
