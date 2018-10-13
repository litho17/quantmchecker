package simplevote_1.com.cyberpointllc.stac.algorithm;

import java.math.BigInteger;

/**
 * Support class for RSA.  Performs exponentiation mod M via montgomery multiplication, as described in
 * http://www.hackersdelight.org/MontgomeryMultiplication.pdf
 */
public class FastModularMultiplier {
    private BigInteger M; // the modulus
    private BigInteger R; // the auxiliary modulus
    // some useful constants based on R and M
    private BigInteger Rminus1; // R-1
    private BigInteger Rinverse; // multiplicative inverse of R (mod M)
    private BigInteger Mstar; // -M^{-1} where M^{-1} is the multiplicative inverse of M (mod R)
    private int w; // R = 2^w

    /**
     * @param floormod
     * @throws IllegalArgumentException
     */
    public FastModularMultiplier(BigInteger floormod) throws IllegalArgumentException {
        this.M = floormod;
        this.w = M.bitLength(); // Assuming the M's bit-length is always a multiple of 8
        if (w % 8 != 0) {
            w = (M.bitLength()/8 + 1)*8;
        }
        this.R = computeR();
        this.Rinverse = R.modInverse(M);
        this.Rminus1 = R.subtract(BigInteger.ONE);
        this.Mstar = R.subtract(M.modInverse(R));
    }

    /**
     * @return R, the auxiliary modulus for M
     * @throws IllegalArgumentException if R can't be computed
     */
    private BigInteger computeR() throws IllegalArgumentException {
        BigInteger R = BigInteger.ONE.shiftLeft(w);
        if ((!R.gcd(M).equals(BigInteger.ONE)) || R.compareTo(M) <= 0) {
            throw new IllegalArgumentException("Unable to compute R for modulus " + M);
        }
        return R;
    }


    /**
     * public multiplication method.  Uses Montgomery multiplication, but this is not efficient.
     *
     * @return a*b(mod M)
     */
    public BigInteger multiply(BigInteger a, BigInteger b) {
        BigInteger aBar;
        BigInteger bBar;
        aBar = translate(a);
        bBar = translate(b);
        BigInteger tmp = fastModularMultiply(aBar, bBar);
        return deTranslate(tmp);
    }

    /**
     * @return x to the y power, computed with square-multiply algorithm and Montgomery multiplication
     */
    public BigInteger exponentiate(BigInteger x, BigInteger y) {

        BigInteger xBar = translate(x);

        BigInteger outcome = translate(BigInteger.ONE);
        for (int k = y.bitLength() - 1; k >= 0; k--) {
            if (y.testBit(k)) {
                outcome = fastModularMultiply(fastModularMultiply(outcome, outcome), xBar);
            } else {
                outcome = fastModularMultiply(outcome, outcome);
            }
        }

        return deTranslate(outcome);
    }

    /*
     * returns the product of aBar and bBar **in Montgomery land**
     */
    private BigInteger fastModularMultiply(BigInteger aBar, BigInteger bBar) {

        BigInteger t = aBar.multiply(bBar);
        BigInteger u = t.multiply(Mstar);
        u = u.and(Rminus1); // mod u by R efficiently
        u = t.add(u.multiply(M));
        u = u.shiftRight(w); // divide by R efficiently
        
        // u is now (t + tM*(modR))M)/R
        if ((u.compareTo(M)) > 0) {
           u = u.mod(M);
        }
	    
        return u;
    }

    // transform a into "Montgomery Land"
    public BigInteger translate(BigInteger a) {
        return a.multiply(R).mod(M);
    }

    // transform back from "Montgomery Land"
    public BigInteger deTranslate(BigInteger u) {
        return u.multiply(Rinverse).mod(M);
    }

}
