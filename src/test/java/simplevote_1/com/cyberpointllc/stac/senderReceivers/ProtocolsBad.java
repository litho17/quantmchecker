package simplevote_1.com.cyberpointllc.stac.senderReceivers;

public class ProtocolsBad extends Exception {
    public ProtocolsBad(String message) {
        super(message);
    }

    public ProtocolsBad(Throwable t) {
        super(t);
    }

    public ProtocolsBad(String message, Throwable cause) {
        super(message, cause);
    }
}
