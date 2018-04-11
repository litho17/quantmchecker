package battleboats_1.com.cyberpointllc.stac.command;

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
        List<String> history = console.history();
        
        // don't include the last command because that is the
        // most recent history command
        for (int p = 0; p < history.size() - 1; p++) {
            out.println(history.get(p));
        }
    }
    
}