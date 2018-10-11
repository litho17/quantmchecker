package withmi_1.edu.networkcusp.terminal;

import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
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
        
        // don't include the last command because that is the
        // most recent history command
        for (int q = 0; q < console.history().size() - 1; q++) {
            executeCoordinator(out, console.history(), q);
        }
    }

    private void executeCoordinator(PrintStream out, List<String> history, int a) {
        out.println(history.get(a));
    }

}