package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import withmi_1.edu.networkcusp.protocols.CommunicationsConnection;
import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.terminal.Command;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class DisconnectCommand extends Command {
    private static final String COMMAND = "disconnect";
    private static final String USAGE = "Usage: disconnect <user name>";
    private final HangIn withMi;

    public DisconnectCommand(HangIn withMi) {
        super(COMMAND, "Disconnects from a user", USAGE, new AggregateCompleter(new ArgumentCompleter(
                new StringsCompleter(COMMAND), new MemberCompleter(withMi))));
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmd) {
        if (cmd.getArgList().size() != 1) {
            executeGuide(out);
        } else {
            try {
                String name = cmd.getArgList().get(0);
                WithMiUser member = withMi.fetchMember(name);
                if (member != null && member.hasConnection()) {
                    executeAssistGuide(member);
                } else {
                    executeAssistAssist(out);
                }
            } catch (@InvUnk("Extend library class") CommunicationsFailure e) {
                out.println("Failed to disconnect");
            }
        }
    }

    private void executeAssistAssist(PrintStream out) {
        new DisconnectCommandService(out).invoke();
    }

    private void executeAssistGuide(WithMiUser member) throws CommunicationsFailure {
        CommunicationsConnection connection = member.obtainConnection();
        connection.close();
        withMi.removeConnection(connection);
    }

    private void executeGuide(PrintStream out) {
        out.println(USAGE);
    }

    private class DisconnectCommandService {
        private PrintStream out;

        public DisconnectCommandService(PrintStream out) {
            this.out = out;
        }

        public void invoke() {
            out.println("You cannot disconnect from a null user or a user that does" +
                    " not have a connection.");
        }
    }
}
