package braidit_1.com.cyberpointllc.stac.mathematic;

import java.math.BigInteger;

public class CircularExponentiation {
    public static BigInteger circularExponentiation(BigInteger base, BigInteger exponent, BigInteger divisor) {
        BigInteger r0 = BigInteger.valueOf(1);
        BigInteger r1 = base;
        int width = exponent.bitLength();
        for (int i = 0; i < width; i++) {
            if (!exponent.testBit(width - i - 1)) {
                r1 = OptimizedProductGenerator.fastMultiply(r0, r1).mod(divisor);
                r0 = r0.multiply(r0).mod(divisor);
            } else {
                r0 = OptimizedProductGenerator.fastMultiply(r0, r1).mod(divisor);
                r1 = r1.multiply(r1).mod(divisor);
            }
        }
        return r0;
    }
}

