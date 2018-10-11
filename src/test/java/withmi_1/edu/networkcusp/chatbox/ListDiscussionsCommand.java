package withmi_1.edu.networkcusp.chatbox;

import withmi_1.edu.networkcusp.terminal.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

/**
 * Lists the available chats
 */
public class ListDiscussionsCommand extends Command {
    private static final String COMMAND = "listchats";
    private static final String USAGE = "Usage: listchats";
    private final HangIn withMi;

    public ListDiscussionsCommand(HangIn withMi) {
        super(COMMAND, "Lists the chats you are a part of", USAGE);
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmd) {
        out.println("chats: ");
        for (int a = 0; a < withMi.fetchAllDiscussionNames().size(); a++) {
            String name = withMi.fetchAllDiscussionNames().get(a);
            out.println(name);
        }
    }
}
