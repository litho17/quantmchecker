package braidit_1.com.cyberpointllc.stac.console;

import jline.console.completer.Completer;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.List;
import java.util.TreeSet;

public class CommandCompleter implements Completer {

    private Display display;

    public CommandCompleter(Display display) {
        this.display = display;
    }
    
    @Override
    public int complete(String buffer, int cursor, List<CharSequence> candidates) {
        // get all the command names
        // we get them fresh each time because they could get stale
        @Inv("+names=-j+c25-c23") TreeSet<String> names = new TreeSet<String>();
        List<Command> obtainCommands = display.obtainCommands();
        c23: for (int j = 0; j < obtainCommands.size(); j++) {
            Command c = obtainCommands.get(j);
            c25: names.add(c.takeName());
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
