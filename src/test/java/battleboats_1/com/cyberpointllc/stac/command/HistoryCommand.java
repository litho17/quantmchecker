package battleboats_1.com.cyberpointllc.stac.command;

import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

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
        @Inv("= (- history it) (- c25 c24)") List<String> history = new ArrayList<>();
        @Iter("<= it console.history") Iterator<String> it = console.history.iterator();
        while (it.hasNext()) {
            String s;
            c24: s = it.next();
            c25: history.add(s);
        }
        
        // don't include the last command because that is the
        // most recent history command
        for (int p = 0; p < history.size() - 1; p++) {
            out.println(history.get(p));
        }
    }
    
}