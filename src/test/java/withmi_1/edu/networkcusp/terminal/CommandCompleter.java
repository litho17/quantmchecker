package withmi_1.edu.networkcusp.terminal;

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
        @Inv("= (- names c) (- c36 c37)") TreeSet<String> names = new TreeSet<String>();
        @Bound("* 2 console.commands") int j;
        @Inv("= (- commands it) (- c104 c103)") List<Command> commands = new ArrayList<>();
        @Iter("<= it console.commands") Iterator<Command> it = console.commands.values().iterator();
        while (it.hasNext()) {
            Command command;
            c103: command = it.next();
            c104: commands.add(command);
        }
        for (@Iter("<= c commands") int c = 0; c < commands.size(); ) {
            Command cmd = commands.get(c);
            c36: names.add(cmd.fetchName());
            c37: c = c + 1;
        }
        if (buffer == null) {
            candidates.addAll(names);
        } else {
            for (String match : names) {
                completeAdviser(buffer, candidates, match);
            }
        }

        if (candidates.size() == 1) {
            completeCoordinator(candidates);
        }

        return candidates.isEmpty() ? -1 : 0;
    }

    private void completeCoordinator(List<CharSequence> candidates) {
        candidates.set(0, candidates.get(0) + " ");
    }

    private void completeAdviser(String buffer, List<CharSequence> candidates, String match) {
        if (match.startsWith(buffer)) {
            completeAdviserHelper(candidates, match);
        }
    }

    private void completeAdviserHelper(List<CharSequence> candidates, String match) {
        candidates.add(match);
    }

}
