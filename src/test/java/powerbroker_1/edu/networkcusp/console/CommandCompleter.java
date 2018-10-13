package powerbroker_1.edu.networkcusp.console;

import jline.console.completer.Completer;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.ArrayList;
import java.util.Iterator;
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
        @Bound("* 2 console.commands") int k;
        @Inv("= (- names q) (- c37 c38)") TreeSet<String> names = new TreeSet<String>();
        @Inv("= (- obtainCommands it) (- c32 c31)") List<Command> obtainCommands = new ArrayList<>();
        @Iter("<= it console.commands") Iterator<Command> it = console.commands.values().iterator();
        while (it.hasNext()) {
            Command cmd;
            c31: cmd = it.next();
            c32: obtainCommands.add(cmd);
        }
        for (@Iter("<= q obtainCommands") int q = 0; q < obtainCommands.size(); ) {
            for (; (q < obtainCommands.size()) && (Math.random() < 0.5); ) {
                Command c = obtainCommands.get(q);
                c37: names.add(c.grabName());
                c38: q = q + 1;
            }
        }
        if (buffer == null) {
            candidates.addAll(names);
        } else {
            for (String match : names) {
                completeFunction(buffer, candidates, match);
            }
        }

        if (candidates.size() == 1) {
            new CommandCompleterAssist(candidates).invoke();
        }

        return candidates.isEmpty() ? -1 : 0;
    }

    private void completeFunction(String buffer, List<CharSequence> candidates, String match) {
        if (match.startsWith(buffer)) {
            completeFunctionUtility(candidates, match);
        }
    }

    private void completeFunctionUtility(List<CharSequence> candidates, String match) {
        candidates.add(match);
    }

    private class CommandCompleterAssist {
        private List<CharSequence> candidates;

        public CommandCompleterAssist(List<CharSequence> candidates) {
            this.candidates = candidates;
        }

        public void invoke() {
            candidates.set(0, candidates.get(0) + " ");
        }
    }
}
