package withmi_1.edu.networkcusp;

import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.terminal.*;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    ExitCommand exitCommand;
    HelpCommand helpCommand;
    HistoryCommand historyCommand;
    RepeatCommand repeatCommand;
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
