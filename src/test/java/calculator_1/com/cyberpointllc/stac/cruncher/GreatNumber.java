package calculator_1.com.cyberpointllc.stac.cruncher;

// TODO: move to math package?

import org.apache.commons.math3.complex.Complex;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Represents an integer as a polynomial over a specified base.
 * (Currently multiplication is the only supported operation.)
 */
public class GreatNumber implements Comparable<GreatNumber> {

    public static final int MULT_CUTOFF = 1000; // size (number of "digits") of integers beyond which we shouldn't use simple multiply
    private int base;
    private int[] coefficients; // coefficients[i] is the coefficient on base^i
    public static final int HIGHEST_SIZE = 50000;
    public static final int HIGHEST_DIVIDEND_RATIO = 10;
    public static final int HIGHEST_DIVIDEND_SIZE = 500;
    private static Transform transform = new Transform();
    private boolean negative = false;

    private static final int[] ZERO_ARRAY = {0};
    private static final int[] ONE_ARRAY = {1};

    public GreatNumber(int[] coefficients, int base, boolean negative) {

        if (coefficients.length > HIGHEST_SIZE) {
            throw new ReportTooGreatDeviationCreator().assignMessage("Integer can have at most " + HIGHEST_SIZE + " digits").composeReportTooGreatDeviation();
        }
        if (coefficients.length == 0) {
            throw new IllegalArgumentException("Integer must have a positive number of digits");
        }
        if (base <= 1) {
            throw new IllegalArgumentException("Base must be at least 2");
        }
        this.base = base;

        for (int j = 0; j < coefficients.length; j++) {
            int coeff = coefficients[j];
            validateCoefficient(coeff); // this will throw an exception if invalid
        }
        this.coefficients = coefficients;
        renewLeadingZeros();
        this.negative = negative;
    }

    // if negative not specified, treat as positive
    public GreatNumber(int[] coefficients, int base) {
        this(coefficients, base, false);
    }

    // constructor for digit strings, base 10
    public GreatNumber(String numbers) {
        numbers = numbers.trim();
        if (numbers.startsWith("-")){
            this.negative = true;
            numbers = numbers.substring(1);
        }
        if (numbers.isEmpty()) {
            throw new IllegalArgumentException("BigInteger string must be non-empty");
        }
        numbers = numbers.replaceFirst("^0+(?!$)", ""); // eliminate leading zeroes
        this.base = 10;
        this.coefficients = new int[numbers.length()];
        for (int j = 0; j < numbers.length(); j++) {
            try {
                int next = Integer.parseInt(String.valueOf(numbers.charAt(numbers.length() - j - 1)));
                validateCoefficient(next); // this will throw an exception if invalid
                this.coefficients[j] = next;
            } catch (NumberFormatException e){
                throw new NumberFormatException("LargeInteger must be created from a string of digits -- illegal character: " + numbers.charAt(numbers.length() - j -1));
            }
        }
    }

    // constructor from an int
    public GreatNumber(int n, int base) {
        this.base = base;
        this.negative = (n < 0);
        int degree = 0;

        if (negative) {
            n = -1*n;
        }
        while (Math.pow(base, degree+1) <= n ){
            degree++;
        }
        coefficients = new int[degree+1];
        for (int k = degree; k >= 0; k--) {
            int factor = (int)Math.pow(base, k);
            int coeff = 0;
            while (factor*(coeff + 1) <= n){
                // if the above operation overflowed
                if (factor*(coeff + 1) < factor*coeff){
                    break;
                }
                coeff++;
            }
            coefficients[k] = coeff;
            n -= coefficients[k]*factor;
        }
    }

    public boolean isNegative() {
        return negative;
    }

    public GreatNumber multiply(GreatNumber other) {
        if (this.base != other.base){
            throw new IllegalArgumentException("Numbers to multiply must have the same base");
        }
       if (this.obtainDegree() > MULT_CUTOFF && other.obtainDegree() > MULT_CUTOFF) {
            return transformMultiply(other);
       } else {
           return easyLogspaceMultiply(other);
       }
    }

    public GreatNumber integrate(GreatNumber other) {
        if (this.base != other.base){
            throw new IllegalArgumentException("Numbers to add must have the same base");
        }
        if (this.negative != other.negative) {
            if (this.negative) {
                return other.subtract(new GreatNumber(this.coefficients, this.base));
            } else {
                return this.subtract(new GreatNumber(other.coefficients, other.base));
            }
        }
        int leastSize = Math.min(this.coefficients.length, other.coefficients.length);
        int[] longerCoefs;
        if (this.coefficients.length > other.coefficients.length) {
            longerCoefs = this.coefficients;
        } else {
            longerCoefs = other.coefficients;
        }
        @Bound("+ 1 (* 2 (+ this.coefficients.length other.coefficients.length))") int i;
        @Inv("= (- sumList a b) (- (+ c153 c160 c164) c154 c161)") List<Integer> sumList = new ArrayList<Integer>();
        int carry = 0;
        int sum = 0;
        // indices where both arrays have elements
        for (@Iter("<= b (+ this.coefficients.length other.coefficients.length)") int b = 0; b < leastSize; ) {
            sum = this.coefficients[b] + other.coefficients[b] + carry;
            carry = sum / base;
            c153: sumList.add(sum % base);
            c154: b = b + 1;
        }
        // indices of the longer array
        for (@Iter("<= a (+ this.coefficients.length other.coefficients.length)") int a = leastSize; a < longerCoefs.length; ) {
            sum = longerCoefs[a] + carry;
            carry = sum / base;
            c160: sumList.add(sum % base);
            c161: a = a + 1;
        }
        if (carry != 0) {
            c164: sumList.add(carry);
        }

        // convert to int[]
        int[] report = convertFromList(sumList);
        return new GreatNumber(report, base, this.negative);
    }

    public GreatNumber subtract(GreatNumber other) {
        if (this.base != other.base){
            throw new IllegalArgumentException("Numbers to subtract must have the same base");
        }
        if (this.negative != other.negative) {
            return this.integrate(new GreatNumber(other.coefficients, other.base, this.negative)); //
        }
        // if we get here, both have the same sign, we proceed to ignore sign and put it back at the end
        int[] bigger;
        int[] smaller;
        boolean responseIsNeg;
        if (hasGreaterMagnitudeThan(other)){
            bigger = this.coefficients;
            smaller = other.coefficients;
            responseIsNeg = this.negative;
        } else if (Arrays.equals(this.coefficients, other.coefficients)) {
            return new GreatNumber("0");
        } else {
            smaller = this.coefficients;
            bigger = other.coefficients;
            responseIsNeg = !this.negative;
        }
        @Bound("* 2 (+ this.coefficients.length other.coefficients.length)") int i;
        @Inv("= (- difference a b) (- (+ c201 c206 c212 c215) c208 c218)") List<Integer> difference = new ArrayList<Integer>();
        int borrowed = 0;
        for (@Iter("<= b (+ this.coefficients.length other.coefficients.length)") int b = 0; b < smaller.length; ) {
            int delta;
            if (bigger[b] - borrowed >= smaller[b]) {
                delta = bigger[b] - borrowed - smaller[b];
                c201: difference.add(delta);
                borrowed = 0;
            } else {
                delta = bigger[b] + base - borrowed - smaller[b];
                borrowed = 1;
                c206: difference.add(delta);
            }
            c208: b = b + 1;
        }
        for (@Iter("<= a (+ this.coefficients.length other.coefficients.length)") int a = smaller.length; a < bigger.length; ) {
            if (bigger[a] >= borrowed) {
                c212: difference.add(bigger[a] - borrowed);
                borrowed = 0;
            } else {
                c215: difference.add(bigger[a] + base - borrowed);
                borrowed = 1;
            }
            c218: a = a + 1;
        }

        int[] report = convertFromList(difference);

        // put sign back in
        return new GreatNumber(report, base, responseIsNeg);
    }

    public GreatNumber divide(GreatNumber divisor) {
        if (this.base != divisor.base){
            throw new IllegalArgumentException("Cannot divide integers with different bases");
        }
        int ratio = (this.obtainDegree()+1)/(divisor.obtainDegree()+1);
        if (divisor.obtainDegree() > 3 && ratio > HIGHEST_DIVIDEND_RATIO) { // TODO: not sure about this divisor check
            throw new ExpensiveFormulaDeviation("Aborting expensive operation--dividend too much larger than divisor");
        } else if (this.obtainDegree()+1 > HIGHEST_DIVIDEND_SIZE) {
            throw new ExpensiveFormulaDeviation("Aborting expensive operation--dividend too large");
        }
        if (divisor.isZero()){
            throw new IllegalArgumentException("Cannot divide by 0");
        }
        if (divisor.hasGreaterMagnitudeThan(this)) {
            return new GreatNumber("0");
        }

        GreatNumber unsignedDivisor = new GreatNumber(divisor.coefficients, divisor.base);
        GreatNumber q = null;

        GreatNumber chunk = new GreatNumber(ZERO_ARRAY, this.base);
        int k = coefficients.length-1;
        while (k >=0) {
            chunk.append(coefficients[k]);
            k--;
            while (unsignedDivisor.hasGreaterMagnitudeThan(chunk) && k >=0) {
                chunk.append(coefficients[k]);
                k--;
                if (q!=null) {
                    q.append(0);
                }
            }
            GreatNumber next = chunk.easyDivide(unsignedDivisor);
            if (q!=null) {
                q.append(next);
            } else {
                q = next;
            }
            chunk = chunk.subtract(next.multiply(unsignedDivisor));
        }
        // put the sign in
        return new GreatNumber(q.coefficients, q.base, this.negative!=divisor.negative);
    }

    public GreatNumber exp(int exponent) {
        if (exponent < 0) {
            throw new IllegalArgumentException("Exponent must be positive");
        }
        if (exponent == 0) {
            int[] one = {1};
            return new GreatNumber(one, this.base);
        }
        if (exponent == 1) {
            return new GreatNumber(this.coefficients, this.base, this.negative);
        }

        if (this.obtainDegree() > HIGHEST_SIZE / (10 * exponent) ) {
            throw new ReportTooGreatDeviationCreator().assignMessage("Unable to compute " + this + " ^ " + exponent).composeReportTooGreatDeviation();
        }
        if (exponent % 2 == 0) {
            return this.multiply(this).exp(exponent / 2);
        } else {
            return this.multiply(this.multiply(this).exp((exponent - 1) / 2));
        }
    }

    public GreatNumber exp(GreatNumber exponent){
        try {
            int exp = Integer.parseInt(exponent.toString());
            return exp(exp);
        } catch (Exception e){
            throw new IllegalArgumentException("Exponent must be an int");
        }

    }

    // find the nth root
    public GreatNumber root(int n) {
        if (!rootArgumentIsValid(n)) {
            throw new IllegalArgumentException("Cannot take " + n + "th root of " + this);
        }
        if (n > HIGHEST_DIVIDEND_SIZE) { // can't handle large n
            throw new ExpensiveFormulaDeviation("Cannot handle nth roots where n > " + HIGHEST_DIVIDEND_SIZE);
        }
        if (this.isZero()) {
            return new GreatNumber(ZERO_ARRAY, base);
        }
        if (this.obtainDegree() > 25) {
            throw new ExpensiveFormulaDeviation("Cannot compute " + n + "th root of " + this);
        }
        GreatNumber ONE = new GreatNumber(ONE_ARRAY, base);
        GreatNumber delta = ONE.integrate(ONE);
        GreatNumber val;
        int intVal = (int) 3*this.obtainDegree()/n;
        if (intVal == 0 ) {
            val = delta;
        } else {
            val = new GreatNumber(String.valueOf(intVal));
        }
        while (!ONE.hasGreaterMagnitudeThan(delta)) {
            GreatNumber p = val.exp(n-1);
            delta = this.divide(p).subtract(val);
            delta = delta.divide(new GreatNumber(n, base));
            val = val.integrate(delta);
            if (val.obtainDegree() >= 5) {
                return rootByContinuedFractions(n);
            }
            if (val.isZero()) { // if val is zero, we're going to divide by zero on the next iteration
                return val;//val = ONE;
            }
        }
        // we might be off by one -- check
        int testing = val.exp(n).compareTo(this);
        if (testing == 1){
            return val.subtract(ONE);
        } else if (testing == -1){
            return val.integrate(ONE);
        } else {
            return val;
        }
    }

    private GreatNumber rootByContinuedFractions(int n) {
        if (this.obtainDegree() > 20) {
            throw new ExpensiveFormulaDeviation("Cannot compute " + n + "th root of " + this);
        }
        GreatNumber x1 = this;
        GreatNumber N = new GreatNumber(String.valueOf(n));
        GreatNumber x2 = this.divide(N);
        GreatNumber ONE = new GreatNumber(ONE_ARRAY, base);
        GreatNumber nMinusOne = N.subtract(ONE);
        int iterations = 0;
        while (!ONE.hasGreaterMagnitudeThan(x1.subtract(x2)))
        {
            int d = x2.obtainDegree();
            if (d == 0) {
                d = 1;
            }
            if (iterations++ > HIGHEST_SIZE /(100*d)) {
                throw new ExpensiveFormulaDeviation("Can't handle " + this + " r " + n);
            }
            x1 = x2;
            x2 = (nMinusOne.multiply(x2).integrate(this.divide(x2.exp(n - 1)))).divide(N);
        }
        return x2;
    }

    public GreatNumber root(GreatNumber n) {
        int nInt;
        try {
            nInt = Integer.parseInt(n.toString());
            try {
                return root(nInt);
            } catch (IllegalArgumentException e) {
                throw e;
            }
        } catch (NumberFormatException e){
            throw new IllegalArgumentException("n for root must be an int: " + n);
        }
    }

    private GreatNumber easyDivide(GreatNumber divisor) {

        GreatNumber one = new GreatNumber(ONE_ARRAY, this.base);

        if (divisor.equals(one)) {
            return new GreatNumber(this.coefficients, this.base, this.negative);
        }

        GreatNumber remainder = new GreatNumber(this.coefficients, this.base);
        int[] zeroArr = {0};
        GreatNumber q = new GreatNumber(zeroArr, base);

        while (!divisor.hasGreaterMagnitudeThan(remainder)) {
            remainder = remainder.subtract(divisor);
            q = q.integrate(one);
        }
        return new GreatNumber(q.coefficients, q.base);
    }

    private void append(int[]  other) {
        if (this.toString().equals("0")) {
            this.coefficients = other;
        } else {
            new GreatNumberHerder(other).invoke();
        }
        renewLeadingZeros();
    }

    private void append(GreatNumber other) {
        append(other.coefficients);
    }

    private void append(int a){
        int[] array = {a};
        append(array);
    }

    private int[] convertFromList(List<Integer> list) {
        int[] report = new int[list.size()];
        for (int b = 0; b < report.length; b++) {
            report[b] = list.get(b);
        }
        return report;
    }

    // ignoring sign, is this bigger?
    protected boolean hasGreaterMagnitudeThan(GreatNumber other){
        if (this.base != other.base){
            throw new IllegalArgumentException("Numbers to compare must have the same base");
        }
        if (this.coefficients.length > other.coefficients.length) {
            return true;
        } else if (other.coefficients.length > this.coefficients.length) {
            return false;
        } else {
            for (int i = this.obtainDegree(); i >=0; ) {
                for (; (i >= 0) && (Math.random() < 0.5); ) {
                    for (; (i >= 0) && (Math.random() < 0.5); i--) {
                        if (this.coefficients[i] > other.coefficients[i]) {
                            return true;
                        } else if (this.coefficients[i] < other.coefficients[i]) {
                            return false;
                        }
                    }
                }
            }
            return false;
        }
    }

    private GreatNumber easyLogspaceMultiply(GreatNumber other) {
        int total = 0;

        int n = this.obtainDegree();
        int m = other.obtainDegree();
        int[] report = new int[n + m + 2];

        for (int b = 0; b < n + m + 1; b++) {
            for (int j = Math.max(0, b - n); j < Math.min(b + 1, m + 1); j++) {
                int myIndex = b - j;
                total += this.coefficients[myIndex] * other.coefficients[j];
            }
            report[b] = total % base;
            total = total / base;
        }
        report[n + m +1] = total % base;
        return new GreatNumber(report, base,this.negative!=other.negative);
    }

    private GreatNumber transformMultiply(GreatNumber other) {
        int n = Math.max(this.obtainDegree(), other.obtainDegree());
        int productContent = 2*(n+1);
        int transformSize = nearestProductOf2(productContent);

        // make complex representations of this and other
        Complex[] thisComplex = this.fetchComplexRepresentation(transformSize);
        Complex[] otherComplex = other.fetchComplexRepresentation(transformSize);

        // take Transform of both
        transform.transform(thisComplex, transformSize, false);
        transform.transform(otherComplex, transformSize, false);

        // take products of coefficients
        Complex[] productOfCoefs = new Complex[transformSize];
        for (int i = 0; i< transformSize; i++){
            productOfCoefs[i] = thisComplex[i].multiply(otherComplex[i]);
        }
        // invert Transform
        transform.transform(productOfCoefs, transformSize, true);
        int[] coefsOfProduct = new int[productContent];
        int carry=0;
        for (int c = 0; c < productContent; c++) {
            coefsOfProduct[c] = (int)Math.round(productOfCoefs[c].getReal());
            coefsOfProduct[c] += carry;
            if (coefsOfProduct[c] >= base) {
                carry = (int)Math.floor(coefsOfProduct[c]/base);
                coefsOfProduct[c] = coefsOfProduct[c] % base;
            } else {
                carry = 0;
            }
        }
        return new GreatNumber(coefsOfProduct, base, this.negative != other.negative);

    }

    private int[] toIntArray(List<Integer> list){
        int[] ret = new int[list.size()];
        for(int b = 0; b < ret.length; b++)
            ret[b] = list.get(b);
        return ret;
    }

    public int obtainDegree()  {
        return coefficients.length - 1;
    }

    public Complex[] fetchComplexRepresentation(int size) {
        Complex[] complexRep = new Complex[size];
        for (int j = 0; j <coefficients.length; j++) {
            complexRep[j] = new Complex(coefficients[j]);
        }
        // pad with 0's up to desired length
        for (int p = coefficients.length; p < size; p++) {
            complexRep[p] = new Complex(0);
        }
        return complexRep;
    }

    // find the smallest number >= n that is a power of 2
    public static int nearestProductOf2(int n) {
        
        int k = (int) Math.ceil(Math.log(n)/Math.log(2));
        int report = (int)Math.pow(2, k);
        return report;
        }

    // throw an exception if coefficient is out of range
    private void validateCoefficient(int p) {
       if ( ( p < 0 ) || (p >= base) ) {
           throw new IllegalArgumentException("Coefficient must be between 0 and " + (base-1) + ", was"  + p);
        }
    }

    @Override
    public String toString() {
        String report = "";

        for (int i=coefficients.length-1; i>=0; i--) {
            report += coefficients[i];
        }
        report.replaceFirst("^0+(?!$)", ""); // eliminate leading zeroes
        if (negative && !report.equals("0")) {
            report = "-" + report;
        }
        if (base != 10){
            report += " base " + base;
        }
        return report;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (!GreatNumber.class.isAssignableFrom(obj.getClass())) {
            return false;
        }
        final GreatNumber other = (GreatNumber) obj;
        if (this.base != other.base) {
            return false;
        }
        return Arrays.equals(this.coefficients, other.coefficients);
    }

    @Override
    public int hashCode() {
        return new BigInteger(this.toString()).hashCode();
    }

    @Override
    public int compareTo(GreatNumber other) {
        if (other == null) {
            throw new IllegalArgumentException("Cannot compare to null");
        }
        if (this.base != other.base) {
            throw new IllegalArgumentException("Cannot compare LargeIntegers with different bases");
        }
        if (this.equals(other)) {
            return 0;
        }
        if (this.hasGreaterMagnitudeThan(other)){
            if (!this.negative){
                return 1;
            } else {
                return -1;
            }
        } else {
            if (other.negative) {
                return 1;
            } else {
                return -1;
            }
        }
    }

    private boolean rootArgumentIsValid(int n) {
        if (negative && isEven(n)) {
            return false;
        }
        if (n <= 0) { // we only take positive roots
            return false;
        }
        return true;
    }

    private boolean isEven(int n) {
        int base = 10;
        String nStr = Integer.toString(n);
        int lastDigit = Integer.parseInt(nStr.substring(nStr.length() - 1));
        for (int j = 0; j <= base/2 - 1; j++) {
        if (lastDigit == j *2) {
                return true;
            }
        }
        return false;
    }

    private void renewLeadingZeros(){
        int k = coefficients.length;
        while (k > 1 && coefficients[k -1] == 0) {
            k--;
        }
        this.coefficients = Arrays.copyOf(coefficients, k);
    }

    public boolean isZero(){
        return Arrays.equals(coefficients, ZERO_ARRAY);
    }

    private class GreatNumberHerder {
        private int[] other;

        public GreatNumberHerder(int[] other) {
            this.other = other;
        }

        public void invoke() {
            int[] tmp = coefficients;
            coefficients = new int[coefficients.length + other.length];
            System.arraycopy(tmp, 0, coefficients, other.length, tmp.length);
            System.arraycopy(other, 0, coefficients, 0, other.length);
        }
    }
}
