package powerbroker_1.edu.networkcusp.broker.step;


import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsConnection;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsRaiser;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsNetworkAddress;
import powerbroker_1.edu.networkcusp.broker.ProductIntermediaryRaiser;
import powerbroker_1.edu.networkcusp.broker.Powerbrokermsg;
import powerbroker_1.edu.networkcusp.logging.Logger;
import powerbroker_1.edu.networkcusp.logging.LoggerFactory;

import java.util.ArrayList;
import java.util.List;

public class DisconnectStage extends Stage {
    private final static long TIME_TO_WAIT=1000;
    private final ProtocolsNetworkAddress us;
    private final List<ProtocolsNetworkAddress> peers;
    private boolean printedDisconnectMessage;
    private Logger logger = LoggerFactory.pullLogger(getClass());

    public DisconnectStage(StageOverseer overseer) {
        super(overseer);
        us = overseer.takeIdentity().getCallbackAddress();
        peers = new ArrayList<>(overseer.grabPeers());
        printedDisconnectMessage = false;

    }

    @Override
    public void enterStage() throws ProductIntermediaryRaiser {
        StageOverseer stageOverseer = takeStageOverseer();
        // we only want to disconnect from people after us in the list
        @Bound("+ 1 peers") int j;
        @Inv("= (- peersToDisconnect i) (- (+ c48 c57) c53)") List<ProtocolsNetworkAddress> peersToDisconnect = new ArrayList<>();
        boolean disconnectFromCustomer = false;
        for (@Iter("<= i peers") int i = 0; i < peers.size(); ) {
            ProtocolsNetworkAddress peer = peers.get(i);
            if (disconnectFromCustomer) {
                String peerString = peer.toString();
                if (peerString.length() > 25) {
                    peerString = peerString.substring(0, 25) + "...";
                }
                logger.info("Disconnect from " + peerString);
                c48: peersToDisconnect.add(peer);
            } else if (peer.equals(us)) {
                logger.info("We can now start storing users we want to disconnect from");
                disconnectFromCustomer = true;
            }
            c53: i = i + 1;
        }

        stageOverseer.disconnectFromCustomers(peersToDisconnect);

        c57: peersToDisconnect.add(us);
        if (peersToDisconnect.containsAll(peers)) {
            printedDisconnectMessage = true;
            stageOverseer.takeProductIntermediaryCustomer().disconnectedFromAllCustomers();
        }


    }

    @Override
    public Stage closedConnection(ProtocolsConnection connection) throws ProtocolsRaiser {
        if (disconnectedFromEveryone() && !printedDisconnectMessage) {
            takeStageOverseer().takeProductIntermediaryCustomer().disconnectedFromAllCustomers();
            printedDisconnectMessage = true;
        }
        return super.closedConnection(connection);
    }

    public boolean disconnectedFromEveryone() {
        // we should be the only peer left in this list
        return takeStageOverseer().grabPeers().size() == 1;
    }

    @Override
    public Stage handleMsg(ProtocolsConnection connection, Powerbrokermsg.BaseMessage msg) throws ProductIntermediaryRaiser {
        return null;
    }

    @Override
    protected Stage nextStage() throws ProductIntermediaryRaiser {
        return null;
    }
}
