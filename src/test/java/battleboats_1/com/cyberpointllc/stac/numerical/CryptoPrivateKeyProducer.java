package battleboats_1.com.cyberpointllc.stac.numerical;

import java.math.BigInteger;

public class CryptoPrivateKeyProducer {
    private BigInteger p;
    private BigInteger q;
    private BigInteger e = BigInteger.valueOf(65537);

    public CryptoPrivateKeyProducer setP(BigInteger p) {
        this.p = p;
        return this;
    }

    public CryptoPrivateKeyProducer fixQ(BigInteger q) {
        this.q = q;
        return this;
    }

    public CryptoPrivateKeyProducer defineE(BigInteger e) {
        this.e = e;
        return this;
    }

    public CryptoPrivateKey makeCryptoPrivateKey() {
        return new CryptoPrivateKey(p, q, e);
    }
}