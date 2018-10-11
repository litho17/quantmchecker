package withmi_1.edu.networkcusp.chatbox;

import withmi_1.edu.networkcusp.terminal.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;

/**
 * Created by ehughes on 4/13/16.
 */
public class PastMembersCommand extends Command {

    private static final String COMMAND = "pastusers";
    private final HangIn withMi;

    public PastMembersCommand(HangIn withMi) {
        super(COMMAND, "Lists disconnected users");
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmd) {
        out.println("Past users: ");
        for (int c = 0; c < withMi.memberConductor.pastMembers.size(); c++) {
            WithMiUser member = withMi.memberConductor.pastMembers.get(c);
            if (member != null) {
                String msg = member.obtainName();
                if (member.hasCallbackAddress()) {
                    msg += "\t" + member.takeCallbackAddress();
                }
                out.println(msg);
            }
        }
    }
}
