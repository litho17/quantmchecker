package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.terminal.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class CurrentMembersCommand extends Command {

    private static final String COMMAND = "currentusers";
    private final HangIn withMi;

    public CurrentMembersCommand(HangIn withMi) {
        super(COMMAND, "Lists the users currently connected");
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmd) {
        out.println("Current users: ");

        @Bound("withMi.memberConductor.nameToMember") int j;
        @Inv("= (- grabCurrentMembers it) (- c116 c115)") List<WithMiUser> grabCurrentMembers = new ArrayList<>();
        @Iter("<= it withMi.memberConductor.nameToMember") Iterator<WithMiUser> it = withMi.memberConductor.nameToMember.values().iterator();
        while (it.hasNext()) {
            WithMiUser u;
            c115: u = it.next();
            c116: grabCurrentMembers.add(u);

        }
        grabCurrentMembers.removeAll(withMi.memberConductor.pastMembers);

        // java.util.List<WithMiUser> grabCurrentMembers = withMi.grabCurrentMembers();
        for (int b = 0; b < grabCurrentMembers.size(); ) {
            for (; (b < grabCurrentMembers.size()) && (Math.random() < 0.6); ) {
                for (; (b < grabCurrentMembers.size()) && (Math.random() < 0.5); ) {
                    for (; (b < grabCurrentMembers.size()) && (Math.random() < 0.6); b++) {
                        WithMiUser member = grabCurrentMembers.get(b);
                        String msg = member.obtainName();
                        if (member.hasCallbackAddress()) {
                            msg += "\t" + member.takeCallbackAddress();
                        }
                        out.println(msg);
                    }
                }
            }
        }
    }
}
