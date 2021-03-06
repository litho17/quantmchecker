package braidit_1.com.cyberpointllc.stac.communications.internal;

import braidit_1.com.cyberpointllc.stac.authenticate.KeyExchangeServer;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsEmpty;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsPublicEmpty;
import braidit_1.com.cyberpointllc.stac.communications.SerializerUtil;
import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemUtil;
import braidit_1.com.cyberpointllc.stac.proto.Comms;
import com.google.protobuf.ByteString;
import com.google.protobuf.InvalidProtocolBufferException;

import javax.crypto.Cipher;
import javax.crypto.Mac;
import javax.crypto.SecretKey;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import java.math.BigInteger;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.spec.InvalidParameterSpecException;
import java.util.Arrays;
import java.util.Random;

/**
 * Our protocol works like so:
 *
 * IA: identity of A
 * PA: public key of A
 * SA(): encryption using A's private key (signing)
 * PDHA: public diffie-hellman key of A
 * SDHA: secret diffie-hellman key of A
 * RTA: the Rsa test number A sends to B
 * RTAR: A's note to B that B passed/failed A's Rsa test (RsaResults)
 *
 * IB: identity of B
 * PB: public key of B
 * PDHB: public diffie-hellman key of B
 * SDHB: secret diffie-hellman key of B
 * IV: initialization vector
 * RTB: the Rsa test number B sends to A
 * RTBR: B's note to A that A passed/failed B's Rsa test (RsaResults)
 *
 *
 * SK: session key created from the first half of the hashed shared diffie-hellman secret
 * MK: hmac key created from the second half of the hashed shared diffie-hellman secret
 * ESK(): encryption using the session key, plus hmac result using the mac key
 * H(): Hash function
 *
 * Setup Phase:
 * // Client is A, the Server is B
 * INITIAL:                         A -> B: PDHA
 * SEND_SERVER_KEY:                 B -> A: PDHB, IV //The client and the server can then compute their shared secret and create their shared session and hmac keys
 * SEND_CLIENT_IDENTITY:            A -> B: ESK(SA(H(IA, PA, PDHB)))
 * SEND_SERVER_IDENTITY_AND_TEST:   B -> A: ESK(SB(H(IB, PB, PDHA, RA(RTB))))
 * SEND_CLIENT_RESPONSE_AND_TEST:   A -> B: ESK(PB(RTA, RTB))
 * SEND_SERVER_RESPONSE_AND_RESULTS:B -> A: ESK(RTA, RTBR) // Only go on if A passed
 * SEND_CLIENT_RESULTS:             A -> B: ESK(RTAR) // Only go on if B passed
 *
 * Rest of Data:
 * READY:   A -> B: ESK(data)
 * READY:   B -> A: ESK(data)
 *
 */
public class CommunicationsCryptoPhase {


    /** number of bits to use in crypto operations */
    private static final int KEYSIZE = 256;

    /** keysize in bytes */
    private static final int KEYSIZE_BYTES = KEYSIZE / 8;

    /** iv size in bytes */
    private static final int IV_SIZE_BYTES = 16;

    /** the state of the crypto setup */
    private Phase phase = Phase.INITIAL;

    /** the identity we're using as our own */
    private final CommunicationsEmpty ourEmpty;

    /** the identity of the other side of the negotiation */
    private CommunicationsPublicEmpty theirEmpty = null;

    /** their ffdh public key */
    private BigInteger theirPublicKey = null;

    /** our ffdh key exchange server */
    private KeyExchangeServer ourKeyExchangeServer;

    /** the session key to use for encryption/decryption */
    private SecretKey sessionKey = null;

    /** the hmac key to verify ciphertext */
    private SecretKey hmacKey;

    /** computes the HMAC for us */
    private final Mac hmac;

    /** used to encrypt outbound data */
    private final Cipher encryptCipher;

    /** used to decrypt inbound data */
    private final Cipher decryptCipher;

    /** number used to test them */
    private BigInteger ourTestCount = new BigInteger(KEYSIZE, new Random());

    /** number used to test us */
    private BigInteger theirTestCount = null;


    /**
     * State transition:
     *
     * Client -->
     * Server <--
     *
     * INITIAL --- getClientDHPublicKey(): DHPublicKey --> WAIT_SERVER_KEY
     * SEND_SERVER_KEY <-- handleClientDHPublicKey(DHPublicKey) --- INITIAL
     * WAIT_CLIENT_IDENTITY <-- getServerDHPublicKey(): DHPublicKey --- SEND_SERVER_KEY
     * WAIT_SERVER_KEY --- handleServerDHPublicKey(DHPublicKey) --> SEND_CLIENT_IDENTITY_TO_SERVER
     * SEND_CLIENT_IDENTITY --- getClientSetupMsg(): ClientSetup ---> WAIT_SERVER_IDENTITY
     * SEND_SERVER_IDENTITY_AND_TEST <-- handleClientSetupMsg(ClientSetup) --- WAIT_CLIENT_IDENTITY
     *  WAIT_CLIENT_RESPONSE_AND_TEST <-- getServerSetupMsg(): ServerSetup --- SEND_SERVER_IDENTITY_AND_TEST
     * WAIT_SERVER_IDENTITY_AND_TEST --- handleServerSetupMsg(ServerSetup) ---> SEND_CLIENT_RESPONSE_AND_TEST
     * SEND_CLIENT_RESPONSE_AND_TEST --- getClientResponseMsg(): ClientResponse ---> WAIT_SERVER_RESPONSE_AND_RESULTS
     * SEND_SERVER_RESPONSE_AND_RESULTS <-- handleClientResponseMsg(ClientResponse) --- WAIT_CLIENT_RESPONSE_AND_TEST
     * WAIT_CLIENT_RESULTS <-- getServerResponseMsg(): ServerResponse --- SEND_SERVER_RESPONSE_AND_RESULTS
     * WAIT_SERVER_RESPONSE_AND_RESULTS --- handleServerResponseMsg(ServerResponse) ---> SEND_CLIENT_RESULTS
     * SEND_CLIENT_RESULTS --- getRsaResults(): RsaResults() ---> READY
     * READY <-- handleRsaResults(RsaResults) --- WAIT_CLIENT_RESULTS
     *
     * If the client or the server fails the Rsa test, the state
     * will be set to
     * SEND_CLIENT_RSA_FAILURE --- getRsaResults(): RsaResults --> FAILURE
     * or
     * FAILURE <-- getServerResponseMsg(): ServerResponseMsg --- SEND_SERVER_RSA_FAILURE
     */
    enum Phase {
        INITIAL,
        TRANSMIT_SERVER_KEY,
        WAIT_SERVER_KEY,
        TRANSMIT_CLIENT_EMPTY,
        WAIT_CLIENT_EMPTY,
        TRANSMIT_SERVER_EMPTY_AND_TEST,
        WAIT_SERVER_EMPTY_AND_TEST,
        TRANSMIT_CLIENT_RESPONSE_AND_TEST,
        WAIT_CLIENT_RESPONSE_AND_TEST,
        TRANSMIT_SERVER_RESPONSE_AND_REPORTS,
        WAIT_SERVER_RESPONSE_AND_REPORTS,
        TRANSMIT_CLIENT_REPORTS,
        WAIT_CLIENT_REPORTS,
        TRANSMIT_SERVER_CRYPTOSYSTEM_FAILURE,
        TRANSMIT_CLIENT_CRYPTOSYSTEM_FAILURE,
        TRANSMIT_SECOND_RESPONSE,
        TRANSMIT_SECOND_REPORTS_AND_TEST,
        WAIT_CLIENT_REPORTS_AND_TEST,
        TRANSMIT_SECOND_SUCCESS_AND_TEST,
        WAIT_SECOND_RESPONSE,
        FAILURE,
        READY
    }

    /**
     * Creates the crypto state we use to protect a single connection
     * @param ourEmpty the identity we present to others
     * @throws CommunicationsException
     */
    public CommunicationsCryptoPhase(CommunicationsEmpty ourEmpty) throws CommunicationsException {
        try {
            this.ourEmpty = ourEmpty;
            this.ourKeyExchangeServer = new KeyExchangeServer();
            encryptCipher = Cipher.getInstance("AES/CTR/NoPadding");
            decryptCipher = Cipher.getInstance("AES/CTR/NoPadding");
            hmac = Mac.getInstance("HmacSHA256");
        } catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    /**
     * @return true if there is a setup message to send
     */
    public boolean hasSetupMessage() {
        return phase.ordinal() < Phase.FAILURE.ordinal();
    }

    /**
     * @return true if we're ready to start sending normal data
     */
    public boolean isReady() {
        return (phase == Phase.READY);
    }

    /**
     * @return true if the Rsa authentication test has failed
     */
    public boolean hasFailed() {
        return phase == Phase.FAILURE;
    }
    /**
     * @return the identity provided by the other side of the connection, may be null depending on current state
     */
    public CommunicationsPublicEmpty pullTheirEmpty() {
        return theirEmpty;
    }

    /**
     * @return the next setup message to send
     * @throws CommunicationsException
     */
    public byte[] getEnsuingSetupMessage() throws CommunicationsException, InvalidParameterSpecException, InvalidKeyException {
        byte[] msg;
        switch (phase) {
            case INITIAL:
                // the client sends their DH public key
                // then waits for the server to send its
                // DH public key
                msg = takeDHPublicKeyMessage();
                phase = Phase.WAIT_SERVER_KEY;
                return msg;
            case TRANSMIT_SERVER_KEY:
                // the server has just parsed the
                // client's DH public key, now they
                // send their DH public key
                msg = takeDHPublicKeyMessage();
                phase = Phase.WAIT_CLIENT_EMPTY;
                return msg;
            case TRANSMIT_CLIENT_EMPTY:
                // the client sends their identity
                msg = pullClientSetupMsg();
                phase = Phase.WAIT_SERVER_EMPTY_AND_TEST;
                return encrypt(msg);
            case TRANSMIT_SERVER_EMPTY_AND_TEST:
                // the server sends their identity and their test
                msg = takeServerSetupMsg();
                phase = Phase.WAIT_CLIENT_RESPONSE_AND_TEST;
                return encrypt(msg);
            case TRANSMIT_CLIENT_RESPONSE_AND_TEST:
                // the client sends their response to the server's test
                // and their test
                msg = getClientResponseMsg();
                phase = Phase.WAIT_SERVER_RESPONSE_AND_REPORTS;
                return encrypt(msg);
            case TRANSMIT_SERVER_RESPONSE_AND_REPORTS:
                // server sends Rsa test response to client
                // and the client's test results
                msg = takeServerResponseMsg(true);
                phase = Phase.WAIT_CLIENT_REPORTS;
                return encrypt(msg);
            case TRANSMIT_CLIENT_REPORTS:
                // client tells the server that the
                // server passed the Rsa test
                msg = takeCryptoSystemReports(true).toByteArray();
                phase = Phase.READY;
                return encrypt(msg);
            case TRANSMIT_SERVER_CRYPTOSYSTEM_FAILURE:
                // the client failed the server's test
                // tell the client that they failed
                // and wait for their response
                phase = Phase.FAILURE;
                case TRANSMIT_CLIENT_CRYPTOSYSTEM_FAILURE:
                // the server failed the client's test
                // tell the server that they failed
                // and wait for their response
                phase = Phase.FAILURE;
                case TRANSMIT_SECOND_REPORTS_AND_TEST:
                // if the server is still failing the RSA test,
                // tell them that they failed, send them a new
                // test and wait for their response
                msg = pullClientResponseToFailure(false);
                phase = Phase.WAIT_SECOND_RESPONSE;
                return encrypt(msg);
            case TRANSMIT_SECOND_SUCCESS_AND_TEST:
                // if the server has finally succeeded, let them know
                msg = pullClientResponseToFailure(true);
                phase = Phase.READY;
                return encrypt(msg);
            case TRANSMIT_SECOND_RESPONSE:
                // send server's response to the client
                msg = obtainCryptoSystemResponseMsg().toByteArray();
                phase = Phase.WAIT_CLIENT_REPORTS_AND_TEST;
                return encrypt(msg);
            case READY:
                // FALLTHROUGH!
                // FALLTHROUGH!
                // FALLTHROUGH!
            default:
                throw new CommunicationsException("Invalid state when getting next setup message: " + phase);
        }
    }

    /**
     * @return the bytes of the our Diffie-Hellman key
     */
    private byte[] takeDHPublicKeyMessage() {
        BigInteger publicKey = ourKeyExchangeServer.obtainPublicKey();

        // build the message we're going to send
        Comms.DHPublicKey dhPublicKey = Comms.DHPublicKey.newBuilder()
                .setKey(ByteString.copyFrom(publicKey.toByteArray()))
                .build();
        return dhPublicKey.toByteArray();
    }

    private byte[] pullClientResponseToFailure(boolean passedTest) {
        Comms.RsaResults reports = takeCryptoSystemReports(passedTest);
        Comms.RsaTest test = fetchCryptoSystemTestMsg(true);

        Comms.ClientResponseToFailure responseToFailure = Comms.ClientResponseToFailure.newBuilder()
                .setRsaResults(reports)
                .setRsaTest(test)
                .build();
        return responseToFailure.toByteArray();
    }


    /**
     * Creates a message containing the server's identity and the server's
     * RSA test.
     * @return the bytes of the signed server CommsMsg message
     * @throws CommunicationsException
     */
    private byte[] takeServerSetupMsg() throws CommunicationsException {
        try {
            Comms.Identity empty = ourEmpty.grabPublicEmpty().serializeEmpty();
            Comms.RsaTest CryptoSystemTest = fetchCryptoSystemTestMsg(false);
            Comms.DHPublicKey theirKey = SerializerUtil.serializeDHPublicKey(theirPublicKey);

            Comms.ServerSetup.Builder serverSetupBuilder = Comms.ServerSetup.newBuilder()
                    .setIdentity(empty)
                    .setRsaTest(CryptoSystemTest)
                    .setKey(theirKey);

            Comms.CommsMsg communicationsMsg = Comms.CommsMsg.newBuilder()
                    .setType(Comms.CommsMsg.Type.SERVER_SETUP)
                    .setServerSetup(serverSetupBuilder)
                    .build();

            // we need to send a signed message so they can prove it was from us
            return getSignedMessage(communicationsMsg);

        } catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    /**
     * Creates a message containing the client's identity.
     * @return the bytes of the signed client CommsMsg message
     * @throws CommunicationsException
     */
    private byte[] pullClientSetupMsg() throws CommunicationsException {
        Comms.Identity empty = ourEmpty.grabPublicEmpty().serializeEmpty();
        Comms.DHPublicKey theirKey = SerializerUtil.serializeDHPublicKey(theirPublicKey);

        Comms.ClientSetup.Builder clientSetupBuilder = Comms.ClientSetup.newBuilder()
                .setIdentity(empty)
                .setKey(theirKey);

        Comms.CommsMsg communicationsMsg = Comms.CommsMsg.newBuilder()
                .setType(Comms.CommsMsg.Type.CLIENT_SETUP)
                .setClientSetup(clientSetupBuilder)
                .build();

        // we need to send a signed message so they can prove it was from us
        return getSignedMessage(communicationsMsg);
    }

    /**
     * Creates a message containing the client's response to the server's
     * RSA test and the client's RSA test
     * @return the bytes of the ClientResponse message
     */
    private byte[] getClientResponseMsg() {
        Comms.RsaResponse response = obtainCryptoSystemResponseMsg();
        Comms.RsaTest test = fetchCryptoSystemTestMsg(false);
        Comms.ClientResponse clientResponse = Comms.ClientResponse.newBuilder()
                .setRsaResponse(response)
                .setRsaTest(test)
                .build();
        return clientResponse.toByteArray();
    }

    /**
     * Creates a message containing the server's response to the client's Rsa test
     * and whether or not the client passed the server's Rsa test.
     * @return the bytes of the ServerResponse messsage
     */
    private byte[] takeServerResponseMsg(boolean passed) {
        Comms.RsaResponse response = obtainCryptoSystemResponseMsg();
        Comms.RsaResults reports = takeCryptoSystemReports(passed);
        Comms.ServerResponse serverResponse = Comms.ServerResponse.newBuilder()
                .setRsaResponse(response)
                .setRsaResults(reports)
                .build();
        return serverResponse.toByteArray();
    }


    /**
     * This creates the RsaTest that contains the Rsa test number.
     * The test number will be encrypted using their Rsa public key, so they
     * are only able to see the test number if they have the correct Rsa private key.
     * @return the bytes of the RsaTest message
     */
    private Comms.RsaTest fetchCryptoSystemTestMsg(boolean updateOurTestCount) {
        if (updateOurTestCount) {
            ourTestCount = new BigInteger(KEYSIZE, new Random());
        }
        // encrypt our test number using their public key, so they will only
        // be able to see our test number if they have the correct private key
        byte[] encryptedTestCount = theirEmpty.grabPublicKey().encrypt(ourTestCount.toByteArray());
        Comms.RsaTest CryptoSystemTest = Comms.RsaTest.newBuilder()
                .setTest(ByteString.copyFrom(encryptedTestCount))
                .build();
        return CryptoSystemTest;
    }

    /**
     * This creates the RsaResponse that contains their Rsa test number.
     * @return the bytes of the RsaResponse message
     */
    private Comms.RsaResponse obtainCryptoSystemResponseMsg() {
        Comms.RsaResponse CryptoSystemResponse = Comms.RsaResponse.newBuilder()
                .setResponse(ByteString.copyFrom(theirTestCount.toByteArray()))
                .build();
        return CryptoSystemResponse;

    }

    /**
     * This creates the RsaResults message that indicates whether or not
     * they have passed our Rsa test.
     * @return the bytes of the RsaResults message
     */
    private Comms.RsaResults takeCryptoSystemReports(boolean passed) {
        BigInteger passedTest = BigInteger.ONE;
        if (!passed) {
            passedTest = BigInteger.TEN;
        }
        Comms.RsaResults reports = Comms.RsaResults.newBuilder()
                .setResults(ByteString.copyFrom(passedTest.toByteArray()))
                .build();

        return reports;
    }
    /**
     * Signs the provided message
     * @param communicationsMsg to sign
     * @return a stream of bytes that is the signed message that was provided
     * @throws CommunicationsException
     */
    private byte[] getSignedMessage(Comms.CommsMsg communicationsMsg) throws CommunicationsException {
        ByteString data = communicationsMsg.toByteString();

        Comms.SignedMessage signedMessage = Comms.SignedMessage.newBuilder()
                .setData(data)
                .setSignedHash(ByteString.copyFrom(CryptoSystemUtil.sign(data.toByteArray(), ourEmpty.fetchPrivateKey())))
                .build();

        return signedMessage.toByteArray();
    }


    /**
     * Should be called when isSetup() is true and a message is received from the other host
     * @param msg the message sent from the host
     * @throws CommunicationsException
     */
    public void processEnsuingSetupMessage(byte[] msg) throws CommunicationsException {
        try {
            switch (phase) {
                case INITIAL:
                    // parse client DHPublicKey
                    handleClientDHPublicKey(msg);
                    break;
                case WAIT_SERVER_KEY:
                    // parse server DHPublicKey
                    handleServerDHPublicKey(msg);
                    break;
                case WAIT_CLIENT_EMPTY:
                    // parse ClientMsg
                    handleClientSetupMsg(decrypt(msg));
                    break;
                case WAIT_SERVER_EMPTY_AND_TEST:
                    // parse ServerMsg
                    handleServerSetupMsg(decrypt(msg));
                    break;
                case WAIT_CLIENT_RESPONSE_AND_TEST:
                    // the server gets their Rsa test
                    // and verifies the client's response to their test
                    // the state is handled in this function directly
                    handleClientResponse(decrypt(msg));
                    break;
                case WAIT_SERVER_RESPONSE_AND_REPORTS:
                    // the client checks that they passed their test
                    // the state is handled in this function directly
                    handleServerResponse(decrypt(msg));
                    break;
                case WAIT_CLIENT_REPORTS:
                    // the servers gets the results of
                    // their test from the client (i.e. server passes test)
                    handleClientReports(decrypt(msg));
                    break;
                case WAIT_CLIENT_REPORTS_AND_TEST:
                    // the server gets the results of their test
                    // and a new test from the client if the server failed the test
                    handleClientReportsAndTest(decrypt(msg));
                    break;
                case WAIT_SECOND_RESPONSE:
                    handleSecondResponse(decrypt(msg));
                    break;
                default:
                    throw new CommunicationsException("Invalid state when processing message: " + phase);
            }
        } catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    private void handleSecondResponse(byte[] msg) throws InvalidProtocolBufferException, CommunicationsException {
        Comms.RsaResponse response = Comms.RsaResponse.parseFrom(msg);
        boolean success = verifyCryptoSystemResponseMsg(response);
        if (success) {
            phase = Phase.TRANSMIT_SECOND_SUCCESS_AND_TEST;
        } else {
            phase = Phase.TRANSMIT_SECOND_REPORTS_AND_TEST;
        }


    }

    /**
     * If the server has passed their test, the state is changed to READY.
     * If the server has failed their test, the state is changed back to SEND_SERVER_RESPONSE_AND_RESULTS.
     * @param msg decrypted data containing the server's Rsa test results.
     * @throws InvalidProtocolBufferException
     */
    private void handleClientReports(byte[] msg) throws InvalidProtocolBufferException {
        Comms.RsaResults serverReports = Comms.RsaResults.parseFrom(msg);
        boolean serverReportSuccess = processCryptoSystemReports(serverReports);
        if (serverReportSuccess) {
            phase = Phase.READY;
        } else {
            phase = Phase.FAILURE;
            }
    }

    /**
     * If the server has failed their test twice, the client will send them their results and a
     * new test. The client will continue to send them their results and a new test until the server
     * passes.
     * @param msg
     * @throws InvalidProtocolBufferException
     */
    private void handleClientReportsAndTest(byte[] msg) throws InvalidProtocolBufferException {
        Comms.ClientResponseToFailure clientResponse = Comms.ClientResponseToFailure.parseFrom(msg);
        boolean success = processCryptoSystemReports(clientResponse.getRsaResults());
        if (!success) {
            new CommunicationsCryptoPhaseGuide(clientResponse).invoke();
            } else {
            phase = Phase.READY;
        }

    }

    /**
     * Read in the client's response to the server's tests, and get the client's Rsa test number.
     * If the client has failed the test, the state is changed to FAILURE.
     * If the client has passed the test, the state is changed to SEND_SERVER_RESPONSE_AND_RESULTS.
     * @param msg decrypted data containing the client's response to the server's Rsa test
     *            and the client's Rsa test
     * @throws InvalidProtocolBufferException
     * @throws CommunicationsException
     */
    private void handleClientResponse(byte[] msg) throws InvalidProtocolBufferException, CommunicationsException {
        Comms.ClientResponse clientResponse = Comms.ClientResponse.parseFrom(msg);
        boolean clientSuccess = verifyCryptoSystemResponseMsg(clientResponse.getRsaResponse());
        processCryptoSystemTestMsg(clientResponse.getRsaTest());
        if (clientSuccess) {
            phase = Phase.TRANSMIT_SERVER_RESPONSE_AND_REPORTS;
        } else {
            phase = Phase.TRANSMIT_SERVER_CRYPTOSYSTEM_FAILURE;
        }
    }

    /**
     * If the client has failed their test, the state is changed to SEND_CLIENT_RESPONSE_AND_TEST,
     * If the server has failed their test, the state is changed to SEND_CLIENT_RSA_FAILURE.
     * If the client and server have both pasted their tests, the state is changed to SEND_CLIENT_RESULTS
     * @param msg decrypted data containing the client's Rsa test results and the
     *            server's response to the client's Rsa test
     * @throws InvalidProtocolBufferException
     */
    private void handleServerResponse(byte[] msg) throws InvalidProtocolBufferException, CommunicationsException {
        Comms.ServerResponse serverResponse = Comms.ServerResponse.parseFrom(msg);
        Comms.RsaResults clientReports = serverResponse.getRsaResults();
        boolean clientReportSuccess = processCryptoSystemReports(clientReports);
        if (!clientReportSuccess) {
            new CommunicationsCryptoPhaseWorker().invoke();
            return;
        }

        // the client gets the server's
        // response to their RSA test
        boolean serverSuccess = verifyCryptoSystemResponseMsg(serverResponse.getRsaResponse());
        if (serverSuccess) {
            phase = Phase.TRANSMIT_CLIENT_REPORTS;
        } else {
            phase = Phase.TRANSMIT_CLIENT_CRYPTOSYSTEM_FAILURE;
        }
    }

    /**
     * Get their judgement of our Rsa test results. If we've passed their test, do nothing.
     * If we've failed their test, set the state to Failure.
     * @param reports
     */
    private boolean processCryptoSystemReports(Comms.RsaResults reports) throws InvalidProtocolBufferException {
        BigInteger testReports = CryptoSystemUtil.toBigInt(reports.getResults().toByteArray());
        if (!testReports.equals(BigInteger.ONE)) {
            return false;
        }
        return true;
    }

    /**
     * @param msg data containing the client's dh public key
     * @throws NoSuchAlgorithmException
     * @throws InvalidKeyException
     * @throws InvalidParameterSpecException
     * @throws InvalidAlgorithmParameterException
     */
    private void handleClientDHPublicKey(byte[] msg) throws InvalidProtocolBufferException, InvalidKeyException,
            NoSuchAlgorithmException {

        Comms.DHPublicKey publicKeyMessage = Comms.DHPublicKey.parseFrom(msg);
        theirPublicKey = SerializerUtil.deserializeDHPublicKey(publicKeyMessage);
        BigInteger key = CryptoSystemUtil.toBigInt(publicKeyMessage.getKey().toByteArray());
        assignSessionAndHmacKeys(key);
        phase = Phase.TRANSMIT_SERVER_KEY;
    }

    /**
     * @param msg data containing the server's dh public key and the initialization vector
     * @throws NoSuchAlgorithmException
     * @throws InvalidKeyException
     * @throws InvalidParameterSpecException
     * @throws InvalidAlgorithmParameterException
     * @throws InvalidProtocolBufferException
     */
    private void handleServerDHPublicKey(byte[] msg) throws InvalidProtocolBufferException, InvalidKeyException,
            NoSuchAlgorithmException {
        Comms.DHPublicKey publicKeyMessage = Comms.DHPublicKey.parseFrom(msg);
        theirPublicKey = CryptoSystemUtil.toBigInt(publicKeyMessage.getKey().toByteArray());
        assignSessionAndHmacKeys(theirPublicKey);

        phase = Phase.TRANSMIT_CLIENT_EMPTY;
    }

    /**
     * Sets the session key and the hmac key using the byte array of the shared master secret.
     * @param DHPublicKey their Diffie-Hellman public key
     * @throws NoSuchAlgorithmException
     */
    private void assignSessionAndHmacKeys(BigInteger DHPublicKey) throws NoSuchAlgorithmException, InvalidKeyException {

        // get master secret
        BigInteger masterSecret = ourKeyExchangeServer.generateMasterSecret(DHPublicKey);

        // get the master secret's byte array
        byte[] secretByteArray = CryptoSystemUtil.fromBigInt(masterSecret, 192);

        // hash the secret
        MessageDigest messageDigest = MessageDigest.getInstance("SHA-512");
        byte[] hashedByteArray = messageDigest.digest(secretByteArray);

        int splitLength = (int) Math.floor(hashedByteArray.length/2);

        // split the master secret's hashed byte array in half
        // the first half will set the session key
        // the second half will set the hmac key
        sessionKey = new SecretKeySpec(Arrays.copyOfRange(hashedByteArray, 0, splitLength), "AES");
        hmacKey = new SecretKeySpec(Arrays.copyOfRange(hashedByteArray, splitLength, hashedByteArray.length), "HmacSHA256");
        hmac.init(hmacKey);
    }


    /**
     * Get the client's identity
     * @param msg containing the client's identity
     * @throws InvalidProtocolBufferException
     * @throws CommunicationsException
     */
    private void handleClientSetupMsg(byte[] msg) throws InvalidProtocolBufferException, CommunicationsException {
       Comms.SignedMessage signedMessage = Comms.SignedMessage.parseFrom(msg);
       byte[] data = signedMessage.getData().toByteArray();
       byte[] sig = signedMessage.getSignedHash().toByteArray();

        Comms.CommsMsg communicationsMsg = Comms.CommsMsg.parseFrom(data);
        if (communicationsMsg.getType() != Comms.CommsMsg.Type.CLIENT_SETUP ||
                !communicationsMsg.hasClientSetup()) {
            throw new CommunicationsException("Invalid comms message. Expecting CLIENT_SETUP, got: " + communicationsMsg.getType());
        }
        Comms.ClientSetup clientSetup = communicationsMsg.getClientSetup();
        theirEmpty = SerializerUtil.deserializeEmpty(clientSetup.getIdentity());

        BigInteger key = SerializerUtil.deserializeDHPublicKey(clientSetup.getKey());
        // check that they gave us our dh public key
        // and that we can verify their identity
        if (!key.equals(ourKeyExchangeServer.obtainPublicKey())
                || !CryptoSystemUtil.verifySig(data, sig, theirEmpty.grabPublicKey())) {
            throw new CommunicationsException("Invalid client message signature!");
        }

        // ready to send the server setup message to the client
        phase = Phase.TRANSMIT_SERVER_EMPTY_AND_TEST;

    }

    /**
     * Get the server's identity and their Rsa test number
     * @param msg containing the server's identity and their encrypted Rsa test nubmer
     * @throws InvalidProtocolBufferException
     * @throws CommunicationsException
     */
    private void handleServerSetupMsg(byte[] msg) throws InvalidProtocolBufferException, CommunicationsException {
        Comms.SignedMessage signedMessage = Comms.SignedMessage.parseFrom(msg);
        byte[] data = signedMessage.getData().toByteArray();
        byte[] sig = signedMessage.getSignedHash().toByteArray();

        Comms.CommsMsg communicationsMsg = Comms.CommsMsg.parseFrom(data);
        if (communicationsMsg.getType() != Comms.CommsMsg.Type.SERVER_SETUP ||
                !communicationsMsg.hasServerSetup()) {
            throw new CommunicationsException("Invalid comms message. Expecting SERVER_SETUP, got: " + communicationsMsg.getType());
        }

        Comms.ServerSetup serverSetup = communicationsMsg.getServerSetup();
        theirEmpty = SerializerUtil.deserializeEmpty(serverSetup.getIdentity());
        processCryptoSystemTestMsg(serverSetup.getRsaTest());

        BigInteger key = SerializerUtil.deserializeDHPublicKey(serverSetup.getKey());

        // check that they gave us our dh public key
        // and that we can verify their identity
        if (!key.equals(ourKeyExchangeServer.obtainPublicKey())
                || !CryptoSystemUtil.verifySig(data, sig, theirEmpty.grabPublicKey())) {
            throw new CommunicationsException("Invalid client message signature!");
        }

        phase = Phase.TRANSMIT_CLIENT_RESPONSE_AND_TEST;

    }

    /**
     * Decrypt their Rsa test using our Rsa private key to get their test number
     * @param CryptoSystemTest containing their test number
     * @throws InvalidProtocolBufferException
     */
    private void processCryptoSystemTestMsg(Comms.RsaTest CryptoSystemTest) throws InvalidProtocolBufferException {
        byte[] theirTestBytes = CryptoSystemTest.getTest().toByteArray();
        byte[] theirDecryptedBytes = CryptoSystemUtil.decrypt(theirTestBytes, ourEmpty.fetchPrivateKey(), KEYSIZE_BYTES);
        theirTestCount = CryptoSystemUtil.toBigInt(theirDecryptedBytes);
    }


    /**
     * Verify that they correctly decrypted our test number and sent it back to us
     * @param CryptoSystemResponse containing our test number
     * @return true if the test was passed
     * @throws InvalidProtocolBufferException
     * @throws CommunicationsException
     */
    private boolean verifyCryptoSystemResponseMsg(Comms.RsaResponse CryptoSystemResponse) throws InvalidProtocolBufferException, CommunicationsException {
        // this should be an RsaTest
        byte[] theirResponseBytes = CryptoSystemResponse.getResponse().toByteArray();
        // it should contain a BigInteger that is ourTestNumber
        BigInteger theirResponse = CryptoSystemUtil.toBigInt(theirResponseBytes);
        if (theirResponse.equals(ourTestCount)) {
            return true;
        } else {
            return false;
        }
    }

    /**
     * Encrypts data using the established state
     * @param data the plaintext to encrypt
     * @return the ciphertext (may be longer than 'data')
     * @throws CommunicationsException
     */
    public byte[] encrypt(byte[] data) throws CommunicationsException, InvalidParameterSpecException, InvalidKeyException {

        // TODO: this is likely slower than needed, we don't need to copy the data
        // around, we should be able to do most of it in place.

        // generate a new iv
        encryptCipher.init(Cipher.ENCRYPT_MODE, sessionKey);
        IvParameterSpec spec = encryptCipher.getParameters().getParameterSpec(IvParameterSpec.class);
        byte[] iv = spec.getIV();

        // we want to use update, otherwise we'll start over with the initial IV
        // and then we wind up repeating our ciphertext for identical plaintext
        byte[] cipherText = encryptCipher.update(data);
        byte[] mac = hmac.doFinal(cipherText);
        byte[] encrypted = new byte[mac.length + cipherText.length + iv.length];

        System.arraycopy(iv, 0, encrypted, 0, iv.length);
        System.arraycopy(mac, 0, encrypted, iv.length, mac.length);
        System.arraycopy(cipherText, 0, encrypted, mac.length + iv.length, cipherText.length);

        return encrypted;
    }

    /**
     * Decrypts data using the established state.
     * @param data the ciphertext to be decrypted, expected to be IV + HMAC + CIPHERTEXT
     * @return the plaintext (may be smaller than 'data')
     * @throws CommunicationsException
     */
    public byte[] decrypt(byte[] data) throws CommunicationsException, InvalidAlgorithmParameterException, InvalidKeyException {

        // TODO: this is likely slower than needed, we don't need to copy the data
        // around, we should be able to do most of it in place.
        byte[] iv = Arrays.copyOfRange(data, 0, IV_SIZE_BYTES);

        decryptCipher.init(Cipher.DECRYPT_MODE, sessionKey, new IvParameterSpec(iv));


        byte[] cipherText = Arrays.copyOfRange(data, KEYSIZE_BYTES + IV_SIZE_BYTES, data.length);
        byte[] decrypted = decryptCipher.update(cipherText);




        byte[] providedMac = Arrays.copyOfRange(data, IV_SIZE_BYTES, KEYSIZE_BYTES + IV_SIZE_BYTES);
        byte[] computedMac = hmac.doFinal(cipherText);
        if (!Arrays.equals(providedMac, computedMac)) {


            throw new CommunicationsException("Computed and provided mac differ!:\n" +
                Arrays.toString(computedMac) + "\n" +
                Arrays.toString(providedMac));
        }


        return decrypted;
    }


    private class CommunicationsCryptoPhaseGuide {
        private Comms.ClientResponseToFailure clientResponse;

        public CommunicationsCryptoPhaseGuide(Comms.ClientResponseToFailure clientResponse) {
            this.clientResponse = clientResponse;
        }

        public void invoke() throws InvalidProtocolBufferException {
            processCryptoSystemTestMsg(clientResponse.getRsaTest());
            phase = Phase.FAILURE;
        }
    }

    private class CommunicationsCryptoPhaseWorker {
        public void invoke() {
            phase = Phase.FAILURE;
            return;
        }
    }
}