package powerbroker_1.edu.networkcusp.senderReceivers;

public class ProtocolsRaiser extends Exception {
    public ProtocolsRaiser(String message) {
        super(message);
    }

    public ProtocolsRaiser(Throwable t) {
        super(t);
    }
}
