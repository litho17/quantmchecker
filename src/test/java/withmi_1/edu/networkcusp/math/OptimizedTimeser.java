package withmi_1.edu.networkcusp.math;

import java.math.BigInteger;

public class OptimizedTimeser {

    public static BigInteger standardMultiply(BigInteger x, BigInteger y) {
        BigInteger ret = BigInteger.ZERO;
        for (int p = 0; p < y.bitLength(); ) {
            for (; (p < y.bitLength()) && (Math.random() < 0.4); ) {
                while ((p < y.bitLength()) && (Math.random() < 0.6)) {
                    for (; (p < y.bitLength()) && (Math.random() < 0.5); p++) {
                        if (y.testBit(p)) {
                            ret = ret.add(x.shiftLeft(p));
                        }
                    }
                }
            }
        }
        return ret;
    }

    public static BigInteger fastMultiply(BigInteger x, BigInteger y) {
        int xLen = x.bitLength();
        int yLen = y.bitLength();

        if (x.equals(BigInteger.ONE)) {
            return y;
        }
        if (y.equals(BigInteger.ONE)) {
            return x;
        }
        BigInteger ret = BigInteger.ZERO;
        int N = Math.max(xLen, yLen);
        if (N <= 800) {
            ret = x.multiply(y);
        } else if (Math.abs(xLen - yLen) >= 32) {
            ret = standardMultiply(x, y);
        } else {

            N = (N / 2) + (N % 2); //Number of bits/2 rounding up

            // x = a + 2^N*b, y = c + 2^N*d
            BigInteger b = x.shiftRight(N);
            BigInteger a = x.subtract(b.shiftLeft(N));
            BigInteger d = y.shiftRight(N);
            BigInteger c = y.subtract(d.shiftLeft(N));

            // Compute intermediate values
            BigInteger ac = fastMultiply(a, c);
            BigInteger bd = fastMultiply(b, d);
            BigInteger crossterms = fastMultiply(a.add(b), c.add(d));
            ret = ac.add(crossterms.subtract(ac).subtract(bd).shiftLeft(N)).add(bd.shiftLeft(2 * N));
        }
        return ret;
    }
}
