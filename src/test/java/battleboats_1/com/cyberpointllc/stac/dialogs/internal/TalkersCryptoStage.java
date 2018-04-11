package battleboats_1.com.cyberpointllc.stac.dialogs.internal;

import battleboats_1.com.cyberpointllc.stac.authorize.KeyExchangeServer;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersEmpty;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersPublicEmpty;
import battleboats_1.com.cyberpointllc.stac.dialogs.DigitizerUtil;
import battleboats_1.com.cyberpointllc.stac.numerical.CryptoUtil;
import battleboats_1.com.cyberpointllc.stac.proto.Comms;
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
public class TalkersCryptoStage {


    /** number of bits to use in crypto operations */
    private static final int KEYSIZE = 256;

    /** keysize in bytes */
    private static final int KEYSIZE_BYTES = KEYSIZE / 8;

    /** iv size in bytes */
    private static final int IV_SIZE_BYTES = 16;

    /** the state of the crypto setup */
    private Stage stage = Stage.INITIAL;

    /** the identity we're using as our own */
    private final TalkersEmpty ourEmpty;

    /** the identity of the other side of the negotiation */
    private TalkersPublicEmpty theirEmpty = null;

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
    private BigInteger ourTestNumber = new BigInteger(KEYSIZE, new Random());

    /** number used to test us */
    private BigInteger theirTestNumber = null;


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
    enum Stage {
        INITIAL,
        SEND_SERVER_KEY,
        WAIT_SERVER_KEY,
        SEND_CLIENT_EMPTY,
        WAIT_CLIENT_EMPTY,
        SEND_SERVER_EMPTY_AND_TEST,
        WAIT_SERVER_EMPTY_AND_TEST,
        SEND_CLIENT_RESPONSE_AND_TEST,
        WAIT_CLIENT_RESPONSE_AND_TEST,
        SEND_SERVER_RESPONSE_AND_REPORTS,
        WAIT_SERVER_RESPONSE_AND_REPORTS,
        SEND_CLIENT_REPORTS,
        WAIT_CLIENT_REPORTS,
        SEND_SERVER_CRYPTO_FAILURE,
        SEND_CLIENT_CRYPTO_FAILURE,
        SEND_SECOND_RESPONSE,
        SEND_SECOND_REPORTS_AND_TEST,
        WAIT_CLIENT_REPORTS_AND_TEST,
        SEND_SECOND_SUCCESS_AND_TEST,
        WAIT_SECOND_RESPONSE,
        FAILURE,
        READY
    }

    /**
     * Creates the crypto state we use to protect a single connection
     * @param ourEmpty the identity we present to others
     * @throws TalkersDeviation
     */
    public TalkersCryptoStage(TalkersEmpty ourEmpty) throws TalkersDeviation {
        try {
            this.ourEmpty = ourEmpty;
            this.ourKeyExchangeServer = new KeyExchangeServer();
            encryptCipher = Cipher.getInstance("AES/CTR/NoPadding");
            decryptCipher = Cipher.getInstance("AES/CTR/NoPadding");
            hmac = Mac.getInstance("HmacSHA256");
        } catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    /**
     * @return true if there is a setup message to send
     */
    public boolean hasSetupMessage() {
        return stage.ordinal() < Stage.FAILURE.ordinal();
    }

    /**
     * @return true if we're ready to start sending normal data
     */
    public boolean isReady() {
        return (stage == Stage.READY);
    }

    /**
     * @return true if the Rsa authentication test has failed
     */
    public boolean hasFailed() {
        return stage == Stage.FAILURE;
    }
    /**
     * @return the identity provided by the other side of the connection, may be null depending on current state
     */
    public TalkersPublicEmpty obtainTheirEmpty() {
        return theirEmpty;
    }

    /**
     * @return the next setup message to send
     * @throws TalkersDeviation
     */
    public byte[] takeFollowingSetupMessage() throws TalkersDeviation, InvalidParameterSpecException, InvalidKeyException {
        byte[] msg;
        switch (stage) {
            case INITIAL:
                // the client sends their DH public key
                // then waits for the server to send its
                // DH public key
                msg = grabDHPublicKeyMessage();
                stage = Stage.WAIT_SERVER_KEY;
                return msg;
            case SEND_SERVER_KEY:
                // the server has just parsed the
                // client's DH public key, now they
                // send their DH public key
                msg = grabDHPublicKeyMessage();
                stage = Stage.WAIT_CLIENT_EMPTY;
                return msg;
            case SEND_CLIENT_EMPTY:
                // the client sends their identity
                msg = obtainClientSetupMsg();
                stage = Stage.WAIT_SERVER_EMPTY_AND_TEST;
                return encrypt(msg);
            case SEND_SERVER_EMPTY_AND_TEST:
                // the server sends their identity and their test
                msg = grabServerSetupMsg();
                stage = Stage.WAIT_CLIENT_RESPONSE_AND_TEST;
                return encrypt(msg);
            case SEND_CLIENT_RESPONSE_AND_TEST:
                // the client sends their response to the server's test
                // and their test
                msg = fetchClientResponseMsg();
                stage = Stage.WAIT_SERVER_RESPONSE_AND_REPORTS;
                return encrypt(msg);
            case SEND_SERVER_RESPONSE_AND_REPORTS:
                // server sends Rsa test response to client
                // and the client's test results
                msg = pullServerResponseMsg(true);
                stage = Stage.WAIT_CLIENT_REPORTS;
                return encrypt(msg);
            case SEND_CLIENT_REPORTS:
                // client tells the server that the
                // server passed the Rsa test
                msg = takeCryptoReports(true).toByteArray();
                stage = Stage.READY;
                return encrypt(msg);
            case SEND_SERVER_CRYPTO_FAILURE:
                // the client failed the server's test
                // tell the client that they failed
                // and wait for their response
                msg = pullServerResponseMsg(false);
                stage = Stage.WAIT_SECOND_RESPONSE;
                return encrypt(msg);
                case SEND_CLIENT_CRYPTO_FAILURE:
                // the server failed the client's test
                // tell the server that they failed
                // and wait for their response
                msg = pullServerResponseMsg(false);
                stage = Stage.WAIT_SECOND_RESPONSE;
                return encrypt(msg);
                case SEND_SECOND_REPORTS_AND_TEST:
                // if the server is still failing the RSA test,
                // tell them that they failed, send them a new
                // test and wait for their response
                msg = takeClientResponseToFailure(false);
                stage = Stage.WAIT_SECOND_RESPONSE;
                return encrypt(msg);
            case SEND_SECOND_SUCCESS_AND_TEST:
                // if the server has finally succeeded, let them know
                msg = takeClientResponseToFailure(true);
                stage = Stage.READY;
                return encrypt(msg);
            case SEND_SECOND_RESPONSE:
                // send server's response to the client
                msg = obtainCryptoResponseMsg().toByteArray();
                stage = Stage.WAIT_CLIENT_REPORTS_AND_TEST;
                return encrypt(msg);
            case READY:
                // FALLTHROUGH!
                // FALLTHROUGH!
                // FALLTHROUGH!
            default:
                throw new TalkersDeviation("Invalid state when getting next setup message: " + stage);
        }
    }

    /**
     * @return the bytes of the our Diffie-Hellman key
     */
    private byte[] grabDHPublicKeyMessage() {
        BigInteger publicKey = ourKeyExchangeServer.fetchPublicKey();

        // build the message we're going to send
        Comms.DHPublicKey dhPublicKey = Comms.DHPublicKey.newBuilder()
                .setKey(ByteString.copyFrom(publicKey.toByteArray()))
                .build();
        return dhPublicKey.toByteArray();
    }

    private byte[] takeClientResponseToFailure(boolean passedTest) {
        Comms.RsaResults reports = takeCryptoReports(passedTest);
        Comms.RsaTest test = pullCryptoTestMsg(true);

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
     * @throws TalkersDeviation
     */
    private byte[] grabServerSetupMsg() throws TalkersDeviation {
        try {
            Comms.Identity empty = DigitizerUtil.serializeEmpty(ourEmpty.takePublicEmpty());
            Comms.RsaTest CryptoTest = pullCryptoTestMsg(false);
            Comms.DHPublicKey theirKey = DigitizerUtil.serializeDHPublicKey(theirPublicKey);

            Comms.ServerSetup.Builder serverSetupProducer = Comms.ServerSetup.newBuilder()
                    .setIdentity(empty)
                    .setRsaTest(CryptoTest)
                    .setKey(theirKey);

            Comms.CommsMsg talkersMsg = Comms.CommsMsg.newBuilder()
                    .setType(Comms.CommsMsg.Type.SERVER_SETUP)
                    .setServerSetup(serverSetupProducer)
                    .build();

            // we need to send a signed message so they can prove it was from us
            return takeSignedMessage(talkersMsg);

        } catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    /**
     * Creates a message containing the client's identity.
     * @return the bytes of the signed client CommsMsg message
     * @throws TalkersDeviation
     */
    private byte[] obtainClientSetupMsg() throws TalkersDeviation {
        Comms.Identity empty = DigitizerUtil.serializeEmpty(ourEmpty.takePublicEmpty());
        Comms.DHPublicKey theirKey = DigitizerUtil.serializeDHPublicKey(theirPublicKey);

        Comms.ClientSetup.Builder clientSetupProducer = Comms.ClientSetup.newBuilder()
                .setIdentity(empty)
                .setKey(theirKey);

        Comms.CommsMsg talkersMsg = Comms.CommsMsg.newBuilder()
                .setType(Comms.CommsMsg.Type.CLIENT_SETUP)
                .setClientSetup(clientSetupProducer)
                .build();

        // we need to send a signed message so they can prove it was from us
        return takeSignedMessage(talkersMsg);
    }

    /**
     * Creates a message containing the client's response to the server's
     * RSA test and the client's RSA test
     * @return the bytes of the ClientResponse message
     */
    private byte[] fetchClientResponseMsg() {
        Comms.RsaResponse response = obtainCryptoResponseMsg();
        Comms.RsaTest test = pullCryptoTestMsg(false);
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
    private byte[] pullServerResponseMsg(boolean passed) {
        Comms.RsaResponse response = obtainCryptoResponseMsg();
        Comms.RsaResults reports = takeCryptoReports(passed);
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
    private Comms.RsaTest pullCryptoTestMsg(boolean updateOurTestNumber) {
        if (updateOurTestNumber) {
            ourTestNumber = new BigInteger(KEYSIZE, new Random());
        }
        // encrypt our test number using their public key, so they will only
        // be able to see our test number if they have the correct private key
        byte[] encryptedTestNumber = theirEmpty.obtainPublicKey().encrypt(ourTestNumber.toByteArray());
        Comms.RsaTest CryptoTest = Comms.RsaTest.newBuilder()
                .setTest(ByteString.copyFrom(encryptedTestNumber))
                .build();
        return CryptoTest;
    }

    /**
     * This creates the RsaResponse that contains their Rsa test number.
     * @return the bytes of the RsaResponse message
     */
    private Comms.RsaResponse obtainCryptoResponseMsg() {
        Comms.RsaResponse CryptoResponse = Comms.RsaResponse.newBuilder()
                .setResponse(ByteString.copyFrom(theirTestNumber.toByteArray()))
                .build();
        return CryptoResponse;

    }

    /**
     * This creates the RsaResults message that indicates whether or not
     * they have passed our Rsa test.
     * @return the bytes of the RsaResults message
     */
    private Comms.RsaResults takeCryptoReports(boolean passed) {
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
     * @param talkersMsg to sign
     * @return a stream of bytes that is the signed message that was provided
     * @throws TalkersDeviation
     */
    private byte[] takeSignedMessage(Comms.CommsMsg talkersMsg) throws TalkersDeviation {
        ByteString data = talkersMsg.toByteString();

        Comms.SignedMessage signedMessage = Comms.SignedMessage.newBuilder()
                .setData(data)
                .setSignedHash(ByteString.copyFrom(CryptoUtil.sign(data.toByteArray(), ourEmpty.obtainPrivateKey())))
                .build();

        return signedMessage.toByteArray();
    }


    /**
     * Should be called when isSetup() is true and a message is received from the other host
     * @param msg the message sent from the host
     * @throws TalkersDeviation
     */
    public void processFollowingSetupMessage(byte[] msg) throws TalkersDeviation {
        try {
            switch (stage) {
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
                    throw new TalkersDeviation("Invalid state when processing message: " + stage);
            }
        } catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    private void handleSecondResponse(byte[] msg) throws InvalidProtocolBufferException, TalkersDeviation {
        Comms.RsaResponse response = Comms.RsaResponse.parseFrom(msg);
        boolean success = validateCryptoResponseMsg(response);
        if (success) {
            stage = Stage.SEND_SECOND_SUCCESS_AND_TEST;
        } else {
            stage = Stage.SEND_SECOND_REPORTS_AND_TEST;
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
        boolean serverReportSuccess = processCryptoReports(serverReports);
        if (serverReportSuccess) {
            stage = Stage.READY;
        } else {
            stage = Stage.SEND_SECOND_RESPONSE;
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
        boolean success = processCryptoReports(clientResponse.getRsaResults());
        if (!success) {
            processCryptoTestMsg(clientResponse.getRsaTest());
            stage = Stage.SEND_SECOND_RESPONSE;
            } else {
            stage = Stage.READY;
        }

    }

    /**
     * Read in the client's response to the server's tests, and get the client's Rsa test number.
     * If the client has failed the test, the state is changed to FAILURE.
     * If the client has passed the test, the state is changed to SEND_SERVER_RESPONSE_AND_RESULTS.
     * @param msg decrypted data containing the client's response to the server's Rsa test
     *            and the client's Rsa test
     * @throws InvalidProtocolBufferException
     * @throws TalkersDeviation
     */
    private void handleClientResponse(byte[] msg) throws InvalidProtocolBufferException, TalkersDeviation {
        Comms.ClientResponse clientResponse = Comms.ClientResponse.parseFrom(msg);
        boolean clientSuccess = validateCryptoResponseMsg(clientResponse.getRsaResponse());
        processCryptoTestMsg(clientResponse.getRsaTest());
        if (clientSuccess) {
            stage = Stage.SEND_SERVER_RESPONSE_AND_REPORTS;
        } else {
            stage = Stage.SEND_SERVER_CRYPTO_FAILURE;
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
    private void handleServerResponse(byte[] msg) throws InvalidProtocolBufferException, TalkersDeviation {
        Comms.ServerResponse serverResponse = Comms.ServerResponse.parseFrom(msg);
        Comms.RsaResults clientReports = serverResponse.getRsaResults();
        boolean clientReportSuccess = processCryptoReports(clientReports);
        if (!clientReportSuccess) {
            stage = Stage.SEND_SECOND_RESPONSE;
            return;
        }

        // the client gets the server's
        // response to their RSA test
        boolean serverSuccess = validateCryptoResponseMsg(serverResponse.getRsaResponse());
        if (serverSuccess) {
            stage = Stage.SEND_CLIENT_REPORTS;
        } else {
            stage = Stage.SEND_CLIENT_CRYPTO_FAILURE;
        }
    }

    /**
     * Get their judgement of our Rsa test results. If we've passed their test, do nothing.
     * If we've failed their test, set the state to Failure.
     * @param reports
     */
    private boolean processCryptoReports(Comms.RsaResults reports) throws InvalidProtocolBufferException {
        BigInteger testReports = CryptoUtil.toBigInt(reports.getResults().toByteArray());
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
        theirPublicKey = DigitizerUtil.deserializeDHPublicKey(publicKeyMessage);
        BigInteger key = CryptoUtil.toBigInt(publicKeyMessage.getKey().toByteArray());
        defineSessionAndHmacKeys(key);
        stage = Stage.SEND_SERVER_KEY;
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
        theirPublicKey = CryptoUtil.toBigInt(publicKeyMessage.getKey().toByteArray());
        defineSessionAndHmacKeys(theirPublicKey);

        stage = Stage.SEND_CLIENT_EMPTY;
    }

    /**
     * Sets the session key and the hmac key using the byte array of the shared master secret.
     * @param DHPublicKey their Diffie-Hellman public key
     * @throws NoSuchAlgorithmException
     */
    private void defineSessionAndHmacKeys(BigInteger DHPublicKey) throws NoSuchAlgorithmException, InvalidKeyException {

        // get master secret
        BigInteger masterSecret = ourKeyExchangeServer.generateMasterSecret(DHPublicKey);

        // get the master secret's byte array
        byte[] secretByteArray = CryptoUtil.fromBigInt(masterSecret, 192);

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
     * @throws TalkersDeviation
     */
    private void handleClientSetupMsg(byte[] msg) throws InvalidProtocolBufferException, TalkersDeviation {
       Comms.SignedMessage signedMessage = Comms.SignedMessage.parseFrom(msg);
       byte[] data = signedMessage.getData().toByteArray();
       byte[] sig = signedMessage.getSignedHash().toByteArray();

        Comms.CommsMsg talkersMsg = Comms.CommsMsg.parseFrom(data);
        if (talkersMsg.getType() != Comms.CommsMsg.Type.CLIENT_SETUP ||
                !talkersMsg.hasClientSetup()) {
            throw new TalkersDeviation("Invalid comms message. Expecting CLIENT_SETUP, got: " + talkersMsg.getType());
        }
        Comms.ClientSetup clientSetup = talkersMsg.getClientSetup();
        theirEmpty = DigitizerUtil.deserializeEmpty(clientSetup.getIdentity());

        BigInteger key = DigitizerUtil.deserializeDHPublicKey(clientSetup.getKey());
        // check that they gave us our dh public key
        // and that we can verify their identity
        if (!key.equals(ourKeyExchangeServer.fetchPublicKey())
                || !CryptoUtil.validateSig(data, sig, theirEmpty.obtainPublicKey())) {
            throw new TalkersDeviation("Invalid client message signature!");
        }

        // ready to send the server setup message to the client
        stage = Stage.SEND_SERVER_EMPTY_AND_TEST;

    }

    /**
     * Get the server's identity and their Rsa test number
     * @param msg containing the server's identity and their encrypted Rsa test nubmer
     * @throws InvalidProtocolBufferException
     * @throws TalkersDeviation
     */
    private void handleServerSetupMsg(byte[] msg) throws InvalidProtocolBufferException, TalkersDeviation {
        Comms.SignedMessage signedMessage = Comms.SignedMessage.parseFrom(msg);
        byte[] data = signedMessage.getData().toByteArray();
        byte[] sig = signedMessage.getSignedHash().toByteArray();

        Comms.CommsMsg talkersMsg = Comms.CommsMsg.parseFrom(data);
        if (talkersMsg.getType() != Comms.CommsMsg.Type.SERVER_SETUP ||
                !talkersMsg.hasServerSetup()) {
            throw new TalkersDeviation("Invalid comms message. Expecting SERVER_SETUP, got: " + talkersMsg.getType());
        }

        Comms.ServerSetup serverSetup = talkersMsg.getServerSetup();
        theirEmpty = DigitizerUtil.deserializeEmpty(serverSetup.getIdentity());
        processCryptoTestMsg(serverSetup.getRsaTest());

        BigInteger key = DigitizerUtil.deserializeDHPublicKey(serverSetup.getKey());

        // check that they gave us our dh public key
        // and that we can verify their identity
        if (!key.equals(ourKeyExchangeServer.fetchPublicKey())
                || !CryptoUtil.validateSig(data, sig, theirEmpty.obtainPublicKey())) {
            throw new TalkersDeviation("Invalid client message signature!");
        }

        stage = Stage.SEND_CLIENT_RESPONSE_AND_TEST;

    }

    /**
     * Decrypt their Rsa test using our Rsa private key to get their test number
     * @param CryptoTest containing their test number
     * @throws InvalidProtocolBufferException
     */
    private void processCryptoTestMsg(Comms.RsaTest CryptoTest) throws InvalidProtocolBufferException {
        byte[] theirTestBytes = CryptoTest.getTest().toByteArray();
        byte[] theirDecryptedBytes = CryptoUtil.decrypt(theirTestBytes, ourEmpty.obtainPrivateKey(), KEYSIZE_BYTES);
        theirTestNumber = CryptoUtil.toBigInt(theirDecryptedBytes);
    }


    /**
     * Verify that they correctly decrypted our test number and sent it back to us
     * @param CryptoResponse containing our test number
     * @return true if the test was passed
     * @throws InvalidProtocolBufferException
     * @throws TalkersDeviation
     */
    private boolean validateCryptoResponseMsg(Comms.RsaResponse CryptoResponse) throws InvalidProtocolBufferException, TalkersDeviation {
        // this should be an RsaTest
        byte[] theirResponseBytes = CryptoResponse.getResponse().toByteArray();
        // it should contain a BigInteger that is ourTestNumber
        BigInteger theirResponse = CryptoUtil.toBigInt(theirResponseBytes);
        if (theirResponse.equals(ourTestNumber)) {
            return true;
        } else {
            return false;
        }
    }

    /**
     * Encrypts data using the established state
     * @param data the plaintext to encrypt
     * @return the ciphertext (may be longer than 'data')
     * @throws TalkersDeviation
     */
    public byte[] encrypt(byte[] data) throws TalkersDeviation, InvalidParameterSpecException, InvalidKeyException {

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
     * @throws TalkersDeviation
     */
    public byte[] decrypt(byte[] data) throws TalkersDeviation, InvalidAlgorithmParameterException, InvalidKeyException {

        // TODO: this is likely slower than needed, we don't need to copy the data
        // around, we should be able to do most of it in place.
        byte[] iv = Arrays.copyOfRange(data, 0, IV_SIZE_BYTES);

        decryptCipher.init(Cipher.DECRYPT_MODE, sessionKey, new IvParameterSpec(iv));


        byte[] cipherText = Arrays.copyOfRange(data, KEYSIZE_BYTES + IV_SIZE_BYTES, data.length);
        byte[] decrypted = decryptCipher.update(cipherText);




        byte[] providedMac = Arrays.copyOfRange(data, IV_SIZE_BYTES, KEYSIZE_BYTES + IV_SIZE_BYTES);
        byte[] computedMac = hmac.doFinal(cipherText);
        if (!Arrays.equals(providedMac, computedMac)) {


            throw new TalkersDeviation("Computed and provided mac differ!:\n" +
                Arrays.toString(computedMac) + "\n" +
                Arrays.toString(providedMac));
        }


        return decrypted;
    }


}