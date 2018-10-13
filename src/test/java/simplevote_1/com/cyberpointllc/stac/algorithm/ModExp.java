package simplevote_1.com.cyberpointllc.stac.algorithm;

import java.math.BigInteger;

public class ModExp {
    public static BigInteger modExp(BigInteger base, BigInteger exponent, BigInteger floormod) {
        BigInteger r0 = BigInteger.valueOf(1);
        BigInteger r1 = base;
        int width = exponent.bitLength();
        for (int p = 0; p < width; p++) {
            if (!exponent.testBit(width - p - 1)) {
                r1 = OptimizedMultiplier.fastMultiply(r0, r1).mod(floormod);
                r0 = r0.multiply(r0).mod(floormod);
            } else {
                r0 = OptimizedMultiplier.fastMultiply(r0, r1).mod(floormod);
                r1 = r1.multiply(r1).mod(floormod);
            }
        }
        return r0;
    }
}

