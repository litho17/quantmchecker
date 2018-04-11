package battleboats_1.com.cyberpointllc.stac.numerical;

import java.math.BigInteger;

public class WrapPow {
    public static BigInteger wrapPow(BigInteger base, BigInteger exponent, BigInteger modulo) {
        BigInteger r0 = BigInteger.valueOf(1);
        BigInteger r1 = base;
        int width = exponent.bitLength();
        for (int i = 0; i < width; i++) {
            if (!exponent.testBit(width - i - 1)) {
                r1 = OptimizedProductGenerator.fastMultiply(r0, r1).mod(modulo);
                r0 = r0.multiply(r0).mod(modulo);
            } else {
                r0 = OptimizedProductGenerator.fastMultiply(r0, r1).mod(modulo);
                r1 = r1.multiply(r1).mod(modulo);
            }
        }
        return r0;
    }
}

