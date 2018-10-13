package simplevote_1.com.cyberpointllc.stac.basicvote.accumulation;

import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsClient;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsConnection;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsBad;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsGuide;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsUnity;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsNetworkAddress;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsServer;
import simplevote_1.com.cyberpointllc.stac.proto.Simplevotemsg;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteBad;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Used by simplevote to handle interaction with other servers to gather complete election results
 */
public class CompilationService implements ProtocolsGuide {
    private final ProtocolsClient client;
    private final ProtocolsServer server;
    private final ProtocolsNetworkAddress nextPeerAddress;

    private final AtomicReference<ProtocolsConnection> nextPeer = new AtomicReference<>();
    private final Set<ProtocolsConnection> connections = new LinkedHashSet<>();
    private final Set<String> awaitedIds = new HashSet<>(); // requestIDs that we've sent out and are awaiting responses for

    // Indicates when it is safe for the client to connect to the peer.
    // This is after another client has connected to this server.
    private final CountDownLatch countDownLatch = new CountDownLatch(1);

    private DirectVoteService directVoteService;
    private OutcomesMessageCreator messageCreator = null;

    public CompilationService(File idFile, File connectionFile) throws DirectVoteBad {
        ProtocolsUnity unity;

        try {
            unity = ProtocolsUnity.loadFromFile(idFile);
        } catch (ProtocolsBad e) {
            throw new DirectVoteBad(e);
        }

        client = new ProtocolsClient(this, unity);
        server = new ProtocolsServer(unity.pullCallbackAddress().takePort(), this, unity, client.grabEventLoopGroup());

        nextPeerAddress = getNextPeerAddress(connectionFile, unity, countDownLatch);
    }

    // Constructor for unit tests only (that don't need an aggregator)
    public CompilationService() {
        client = null;
        server = null;
        nextPeerAddress = null;
    }

    public void defineDirectVoteService(DirectVoteService directVoteService) {
        this.directVoteService = directVoteService;

        messageCreator = new OutcomesMessageCreator(directVoteService);
    }

    public void gatherOutcomes(String surveyId, SurveyOutcomes outcomes) throws DirectVoteBad {
        ProtocolsConnection peer = grabPeer();

        if (peer != null) { // if there is another server
            awaitedIds.add(outcomes.obtainRequestId());

            try {
                Simplevotemsg.ElectionResultsMessage msg = messageCreator.buildMessage(outcomes);
                peer.write(msg.toByteArray());
            } catch (ProtocolsBad e) {
                throw new DirectVoteBad(e);
            }
        } else { // just persist results, so they'll be available upon request
            directVoteService.addOrUpdateOutcomes(outcomes);
        }
    }

    @Override
    public void handle(ProtocolsConnection connection, byte[] data) throws ProtocolsBad {
        try {
            Simplevotemsg.ElectionResultsMessage msg = Simplevotemsg.ElectionResultsMessage.parseFrom(data);
            SurveyOutcomes partialOutcomes = new SurveyOutcomes(msg);
            String requestId = partialOutcomes.obtainRequestId();

            if (awaitedIds.contains(requestId)) {
                directVoteService.addOrUpdateOutcomes(partialOutcomes);
                awaitedIds.remove(requestId);
            } else {
                // Since we received a message, there must be a peer to pass on to
                ProtocolsConnection peer = grabPeer();

                if (peer != null) {
                    // Add our results and send on to next peer
                    String surveyId = partialOutcomes.takeSurveyId();

                    SurveyOutcomes localOutcomes = directVoteService.fetchLocalSurveyOutcomes(surveyId);
                    partialOutcomes.addOutcomes(localOutcomes);

                    peer.write(messageCreator.buildMessage(partialOutcomes).toByteArray());
                }

            }
        } catch (Exception e) {
            throw new ProtocolsBad(e);
        }
    }

    @Override
    public void newConnection(ProtocolsConnection connection) throws ProtocolsBad {
        if (connection != null) {
            System.out.println("Server Connection from " + connection.fetchTheirUnity().fetchCallbackAddress());
        }

        // Signal that the peer can be connected to now
        countDownLatch.countDown();
    }

    @Override
    public void closedConnection(ProtocolsConnection connection) throws ProtocolsBad {
        if (connection != null) {
            System.out.println("Server Connection closed from " + connection.fetchTheirUnity().fetchCallbackAddress());
        }
    }

    public ProtocolsConnection connect(ProtocolsNetworkAddress other) throws ProtocolsBad {
        ProtocolsConnection newConnection = null;
        int attempts = 0;

        while ((newConnection == null) && (attempts++ < 3)) {
            System.out.println("Connection attempt " + attempts);

            try {
                newConnection = client.connect(other);
            } catch (ProtocolsBad e) {
                try {
                    System.out.println("Failed to connect to " + other + "; retrying...");
                    Thread.sleep(3000);
                } catch (InterruptedException ex) {
                    System.err.println("sleep interrupted");
                }
            }
        }

        if (newConnection == null) {
            System.out.println("Connection failed to " + other);
        } else {
            connections.add(newConnection);
        }

        return newConnection;
    }

    public void start() throws Exception {
        if (directVoteService == null) {
            throw new IllegalStateException(getClass().getSimpleName() + " is not configured correctly");
        }

        try {
            server.serve();
            countDownLatch.await();
            grabPeer();
        } catch (ProtocolsBad e) {
            throw new Exception(e);
        }
    }

    public void stop() {
        Set<ProtocolsConnection> copyConnections = new LinkedHashSet<>();
        synchronized (connections) { // remove all connections atomically
            copyConnections.addAll(connections);
            connections.clear();
        }

        nextPeer.set(null);

        for (ProtocolsConnection connection : copyConnections) {
            stopCoordinator(connection);
        }

        server.close();
        client.close();
    }

    private void stopCoordinator(ProtocolsConnection connection) {
        try {
            System.out.println("Closing connection with " + connection.fetchTheirUnity().getId());
            connection.close();
        } catch (ProtocolsBad e) {
            System.err.println("Unable to close connection to " + connection.fetchTheirUnity() + ",error=" + e);
        }
    }

    private ProtocolsConnection grabPeer() {
        if ((nextPeer.get() == null) && (nextPeerAddress != null)) {
            nextPeer.compareAndSet(null, obtainNextPeer(nextPeerAddress));
        }

        return nextPeer.get();
    }

    private ProtocolsConnection obtainNextPeer(ProtocolsNetworkAddress peer) {
        System.out.println("Attempting to connect to " + peer);

        try {
            ProtocolsConnection nextPeer = connect(peer);

            if (nextPeer != null) {
                return nextPeer;
            }
        } catch (Exception e) {
            System.err.println(e.getMessage());
        }

        return null;
    }

    private static ProtocolsNetworkAddress getNextPeerAddress(File connectionFile,
                                                              ProtocolsUnity unity,
                                                              CountDownLatch countDownLatch) throws DirectVoteBad {
        List<ProtocolsNetworkAddress> peers = fetchPeers(connectionFile);
        int unityIndex = peers.indexOf(unity.pullCallbackAddress());

        if ((unityIndex == -1) && !peers.isEmpty()) {
            throw new DirectVoteBad("ConnectionFile does not contain identity address: " + unity.pullCallbackAddress());
        }

        // Signal the first entry in the index to start peer connection right away
        if (unityIndex == 0) {
            countDownLatch.countDown();
        }

        // My address is the only one; so there are no peers
        if ((unityIndex == 0) && (peers.size() == 1)) {
            return null;
        }

        // Find the next peer (circularly)
        int index = (unityIndex + 1) % peers.size();

        return peers.get(index);
    }

    private static List<ProtocolsNetworkAddress> fetchPeers(File connectionFile) throws DirectVoteBad {
        List<ProtocolsNetworkAddress> peers = new ArrayList<>();

        if ((connectionFile != null) && connectionFile.exists() && connectionFile.canRead()) {
            try (BufferedReader reader = new BufferedReader(new FileReader(connectionFile))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    String[] parts = line.split(":");

                    if (!line.trim().startsWith("#") && (parts.length == 2)) {
                        ProtocolsNetworkAddress peer = new ProtocolsNetworkAddress(parts[0], Integer.valueOf(parts[1]));

                        if (peers.contains(peer)) {
                            throw new IllegalArgumentException("Peer from connection file must not be repeated: " + peer);
                        }

                        peers.add(peer);
                    }
                }
            } catch (Exception e) {
                throw new DirectVoteBad(e);
            }
        }

        return peers;
    }
}
