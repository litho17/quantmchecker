package calculator_1.com.cyberpointllc.stac.permission;

import calculator_1.com.cyberpointllc.stac.mathematic.ModularExp;

import java.math.BigInteger;
import java.security.SecureRandom;

/*
 * This is the class that performs the most basic DH operations.  
 * Namely it has a secret exponent x which acts as a key.
 * Our public key is A = g^x mod m, where g and m are agreed upon a priori.
 * To agree on a master secret, a client sends his public key B = g^y mod m for some secret y.
 * Server computes a shared master secret B^x mod m = (g^y)^x mod m = g^xy mod m.
 * Client computes shared secret by A^y mod m = (g^x)^y mod m = g^xy mod m.
 * In a real host program, these values should be hashed to give a symmertric key, and possibly a HMAC key.
 */
public class CodeExchangeController {
    private BigInteger secretCode;
    private BigInteger factor;
    private BigInteger generator;
    private BigInteger publicCode;
    private static final String DEFAULT_FACTOR = "0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA237327FFFFFFFFFFFFFFFF";
    private static final BigInteger DEFAULT_GENERATOR = BigInteger.valueOf(2);

    public CodeExchangeController(BigInteger secretCode, BigInteger factor, BigInteger generator) {
        this.secretCode = secretCode;
        this.factor = factor;
        this.generator = generator;
        this.publicCode = this.generator.modPow(this.secretCode, this.factor);
    }

    // Constructor for user specified key exponent, modulus and generator
    // Should be used rarely
    public CodeExchangeController(String secretCode, String factor, String generator) {
        this(stringToBigInt(secretCode), stringToBigInt(factor), stringToBigInt(generator));
    }

    // Constructor that uses the modp1536 group and a passed in secret exponent.
    // This will be the one used in most of our attacks
    public CodeExchangeController(String secretCode) {
        this(stringToBigInt(secretCode), stringToBigInt(DEFAULT_FACTOR), DEFAULT_GENERATOR);
    }

    // Constructor that uses the modp1536 group and a random secret exponent
    public CodeExchangeController() {
        this(composeRandomSecret(), stringToBigInt(DEFAULT_FACTOR), DEFAULT_GENERATOR);
    }
    
    public BigInteger getFactor() {
        return factor;
    }

    public BigInteger getGenerator() {
        return generator;
    }

    public BigInteger obtainPublicCode() {
        return publicCode;
    }

    // Fundamental operation in finite field Diffie-Hellman key exchanges.  
    // Raises the submitted public key to our secret exponent.
    // Just using the default Java modPow which is not designed for cryptography.
    public BigInteger generateMasterSecret(BigInteger userPublic) {
        return ModularExp.modularExp(userPublic, secretCode, factor);
    }


    private static BigInteger stringToBigInt(String count) {
        if (count.startsWith("0x")) {
            return new BigInteger(count.substring(2), 16);
        }
        return new BigInteger(count);
    }

    private static BigInteger composeRandomSecret() {
        SecureRandom r = new SecureRandom();
        byte[] randbytes = new byte[8];
        r.nextBytes(randbytes);
        // we want the BigInteger to be positive
        return new BigInteger(1, randbytes);
    }

}
