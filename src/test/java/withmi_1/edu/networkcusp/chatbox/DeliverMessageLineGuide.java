package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.terminal.LineGuide;

import java.io.PrintStream;

public class DeliverMessageLineGuide implements LineGuide {
    private final HangIn withMi;

    public DeliverMessageLineGuide(HangIn withMi) {
        this.withMi = withMi;
    }

    @Override
    public void handleLine(String line, PrintStream out) {
        try {
            this.withMi.deliverMessage(line);
        } catch (@InvUnk("Extend library class") CommunicationsFailure e) {
            out.println("- Could not send message: " + e.getMessage());
        }
    }
}
