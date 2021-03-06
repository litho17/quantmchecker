package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.terminal.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class ConnectCommand extends Command {
    private static final String COMMAND = "connect";
    private static final String USAGE = "Usage: connect <host> <port>";
    private final HangIn withMi;

    public ConnectCommand(HangIn withMi) {
        super(COMMAND, "Connects to the specified host", USAGE);
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() != 2) {
            out.println(USAGE);
        } else {
            String host = cmdLine.getArgList().get(0);
            String port = cmdLine.getArgList().get(1);
            try {
                withMi.connect(host, Integer.parseInt(port), false);
            } catch (@InvUnk("Extend library class") CommunicationsFailure e) {
                out.println("Error connecting: " + e.getMessage());
            }
        }
    }
}
