package SnapBuddy_1.com.cyberpointllc.stac.console;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class HistoryCommand extends Command {

    private static final String NAME = "history";

    private Console console;

    public HistoryCommand(Console console) {
        super(NAME, "prints the command history", NAME);
        this.console = console;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        @Bound("console.history") int j;
        @Inv("= (- history it) (- c31 c30)") List<String> history = new ArrayList<>();
        @Iter("<= it console.history") Iterator<String> it = console.history.iterator();
        while (it.hasNext()) {
            String s;
            c30: s = it.next();
            c31: history.add(s);
        }
        // most recent history command
        for (int i = 0; i < history.size() - 1; i++) {
            executeHelper(history, out, i);
        }
    }

    private void executeHelper(List<String> history, PrintStream out, int i) {
        out.println(history.get(i));
    }
}
