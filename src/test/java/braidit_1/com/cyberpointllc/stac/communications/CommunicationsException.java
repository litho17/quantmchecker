package braidit_1.com.cyberpointllc.stac.communications;

public class CommunicationsException extends Exception {
    public CommunicationsException(String message) {
        super(message);
    }

    public CommunicationsException(Throwable t) {
        super(t);
    }

    public CommunicationsException(String message, Throwable cause) {
        super(message, cause);
    }
}
