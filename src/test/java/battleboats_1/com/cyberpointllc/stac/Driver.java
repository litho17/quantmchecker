package battleboats_1.com.cyberpointllc.stac;

import battleboats_1.com.cyberpointllc.stac.command.*;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    RepeatCommand repeatCommand;
    ExitCommand exitCommand;
    HelpCommand helpCommand;
    HistoryCommand historyCommand;
    ScriptCommand scriptCommand;
    PrintStream out;
    CommandLine cmdLine;

    public void main(List<Command> input) {
        @Inv("= (- console.history it) (- c32 c30)") Console console;
        console = null;
        @Bound("input") int i;
        @Iter("<= it input") Iterator<Command> it = input.iterator();
        while (it.hasNext()) {
            Command c;
            c30: c = it.next();
            c.execute(out, cmdLine);
            c32: console.history.add(c.toString());
        }
    }
}
