package braidit_1.com.cyberpointllc.stac.console;

import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class HistoryCommand extends Command {
    private static final String NAME = "history";
    private Display display;
    
    public HistoryCommand(Display display) {
        super(NAME, "prints the command history", NAME);
        this.display = display;
    }
    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        
        // don't include the last command because that is the
        // most recent history command
        for (int p = 0; p < display.history().size() - 1; p++) {
            out.println(display.history().get(p));
        }
    }
    
}