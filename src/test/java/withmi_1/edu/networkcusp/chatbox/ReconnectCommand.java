package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.protocols.CommunicationsPublicIdentity;
import withmi_1.edu.networkcusp.terminal.Command;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;


public class ReconnectCommand extends Command {
    private static final String COMMAND = "reconnect";
    private static final String USAGE = "Usage: reconnect <user's name>";
    private final HangIn withMi;

    public ReconnectCommand(HangIn withMi) {
        super(COMMAND, "Reconnects to the specified user", USAGE, new AggregateCompleter(new ArgumentCompleter(
                new StringsCompleter(COMMAND), new MemberCompleter(withMi))));
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() != 1) {
            out.println(USAGE);
        } else {
            String name = cmdLine.getArgList().get(0);
            WithMiUser theirMember = withMi.fetchMember(name);
            if (theirMember != null) {
                CommunicationsPublicIdentity theirIdentity = theirMember.getIdentity();
                try {
                    withMi.connect(theirIdentity.obtainCallbackAddress(), true);
                } catch (@InvUnk("Extend library class") CommunicationsFailure e) {
                    out.println("Error connecting: " + e.getMessage());
                }
            } else {
                out.println("Not a valid user");
            }
        }

    }
}
