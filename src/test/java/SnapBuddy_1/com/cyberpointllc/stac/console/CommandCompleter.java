package SnapBuddy_1.com.cyberpointllc.stac.console;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;
import jline.console.completer.Completer;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class CommandCompleter implements Completer {

    private Console console;

    public CommandCompleter(Console console) {
        this.console = console;
    }

    @Override
    public int complete(String buffer, int cursor, List<CharSequence> candidates) {
        // get all the command names
        // we get them fresh each time because they could get stale

        @Bound("* 2 console.commands") int i;
        @Inv("= (- commands it) (- c57 c56)") List<Command> commands = new ArrayList<>();
        @Iter("<= it console.commands") Iterator<Command> it = console.commands.values().iterator();
        while (it.hasNext()) {
            Command cmd;
            c56: cmd = it.next();
            c57: commands.add(cmd);
        }

        @Inv("= (- names it1) (- c39 c38)") TreeSet<String> names = new  TreeSet<String>();
        @Iter("<= it1 commands") Iterator<Command> it1 = commands.iterator();
        while (it1.hasNext()) {
            Command c;
            c38: c = it1.next();
            c39: names.add(c.getName());
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
}
