package battleboats_1.com.cyberpointllc.stac.command;

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
        @Inv("= (- names b) (- c44 c45)") TreeSet<String> names = new TreeSet<String>();
        // List<Command> pullCommands = console.pullCommands();
        @Bound("* 2 (+ console.permanentCommands console.currentCommands)") int i;
        @Inv("= (- pullCommands it1 it2) (- (+ c129 c134) c128 c133)") List<Command> pullCommands = new ArrayList<>();
        @Iter("<= it1 console.currentCommands") Iterator<Command> it1 = console.currentCommands.values().iterator();
        Command c;
        while (it1.hasNext()) {
            c128: c = it1.next();
            c129: pullCommands.add(c);
        }
        @Iter("<= it2 console.permanentCommands")Iterator<Command> it2 = console.permanentCommands.values().iterator();
        while (it2.hasNext()) {
            c133: c = it2.next();
            c134: pullCommands.add(c);
        }
        for (@Iter("<= b pullCommands") int b = 0; b < pullCommands.size(); ) {
            while ((b < pullCommands.size()) && (Math.random() < 0.5)) {
                for (; (b < pullCommands.size()) && (Math.random() < 0.4);) {
                    Command c2 = pullCommands.get(b);
                    c44: names.add(c2.grabName());
                    c45: b = b + 1;
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
}
