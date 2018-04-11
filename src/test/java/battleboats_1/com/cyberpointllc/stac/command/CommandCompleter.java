package battleboats_1.com.cyberpointllc.stac.command;

import jline.console.completer.Completer;

import java.util.List;
import java.util.TreeSet;

public class CommandCompleter implements Completer {

    private Console console;

    public CommandCompleter(Console console) {
        this.console = console;
    }
    
    @Override
    public int complete(String buffer, int cursor, List<CharSequence> candidates) {
        // get all the command names
        // we get them fresh each time because they could get stale
        TreeSet<String> names = new TreeSet<String>();
        List<Command> pullCommands = console.pullCommands();
        for (int b = 0; b < pullCommands.size(); ) {
            while ((b < pullCommands.size()) && (Math.random() < 0.5)) {
                for (; (b < pullCommands.size()) && (Math.random() < 0.4); b++) {
                    new CommandCompleterCoordinator(names, pullCommands, b).invoke();
                }
            }
        }
        if (buffer == null) {
            candidates.addAll(names);
        } else {
            for (String match : names) {
                if (match.startsWith(buffer)) {
                    candidates.add(match);
                }
            }
        }

        if (candidates.size() == 1) {
            candidates.set(0, candidates.get(0) + " ");
        }

        return candidates.isEmpty() ? -1 : 0;
    }

    private class CommandCompleterCoordinator {
        private TreeSet<String> names;
        private List<Command> pullCommands;
        private int p;

        public CommandCompleterCoordinator(TreeSet<String> names, List<Command> pullCommands, int p) {
            this.names = names;
            this.pullCommands = pullCommands;
            this.p = p;
        }

        public void invoke() {
            Command c = pullCommands.get(p);
            names.add(c.grabName());
        }
    }
}
