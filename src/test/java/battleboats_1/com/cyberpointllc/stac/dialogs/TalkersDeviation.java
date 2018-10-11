package battleboats_1.com.cyberpointllc.stac.dialogs;

public class TalkersDeviation extends Exception {
    public TalkersDeviation(String message) {
        super(message);
    }

    public TalkersDeviation(Throwable t) {
        super(t);
    }

    public TalkersDeviation(String message, Throwable cause) {
        super(message, cause);
    }
}
