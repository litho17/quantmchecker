package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.terminal.Command;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Switches to the specified group chat.
 * A user can only switch to a chat that they are already a part of.
 */
public class AccessDiscussionCommand extends Command {
    private static final String COMMAND = "joinchat";
    private static final String USAGE = "Usage: joinchat <chat name>";
    private final HangIn withMi;

    public AccessDiscussionCommand(HangIn withMi) {
        super(COMMAND, "Joins the specified chat", USAGE, new AggregateCompleter(new ArgumentCompleter(
                new StringsCompleter(COMMAND), new AccessDiscussionCompleter(withMi))));
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmd) {
        if (cmd.getArgList().size() != 1) {
            executeEntity(out);
        } else {
            String discussionName = cmd.getArgList().get(0);

            // check that the chat exists
            @Bound("withMi.discussionConductor.nameToDiscussion") int i;
            @Inv("= (- discussionNames it) (- c46 c45)") List<String> discussionNames = new ArrayList<>();
            @Iter("<= it withMi.discussionConductor.nameToDiscussion") Iterator<String> it = withMi.discussionConductor.nameToDiscussion.keySet().iterator();
            while (it.hasNext()) {
                String s;
                c45: s = it.next();
                c46: discussionNames.add(s);
            }
            if (discussionNames.contains(discussionName)) {
                // join chat associated with given name

                withMi.discussionConductor.switchToDiscussion(discussionName);

                out.println("joined " + discussionName);

                // print all unread messages
                if (withMi.discussionConductor.currentDiscussion.readUnreadMessages().isEmpty()) {
                    out.println("no unread messsages");
                } else {
                    out.println("unread messages: ");
                    for (int b = 0; b < withMi.discussionConductor.currentDiscussion.readUnreadMessages().size(); ) {
                        while ((b < withMi.discussionConductor.currentDiscussion.readUnreadMessages().size()) && (Math.random() < 0.4)) {
                            for (; (b < withMi.discussionConductor.currentDiscussion.readUnreadMessages().size()) && (Math.random() < 0.6); ) {
                                for (; (b < withMi.discussionConductor.currentDiscussion.readUnreadMessages().size()) && (Math.random() < 0.6); b++) {
                                    executeHelper(out, withMi.discussionConductor.currentDiscussion.readUnreadMessages(), b);
                                }
                            }
                        }
                    }
                }
            } else {
                executeAssist(out, discussionName);
            }
        }
    }

    private void executeAssist(PrintStream out, String discussionName) {
        out.println("No chat exists with the name " + discussionName);
    }

    private void executeHelper(PrintStream out, List<String> unreadMessages, int a) {
        String message = unreadMessages.get(a);
        out.println(message);
    }

    private void executeEntity(PrintStream out) {
        out.println(USAGE);
        out.println("The command 'joinchat' allows you to switch to an existing chat");
    }
}
