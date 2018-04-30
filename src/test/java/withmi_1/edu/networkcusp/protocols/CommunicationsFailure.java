package withmi_1.edu.networkcusp.protocols;

public class CommunicationsFailure extends Exception {
    public CommunicationsFailure(String message) {
        super(message);
    }

    public CommunicationsFailure(Throwable t) {
        super(t);
    }
}
