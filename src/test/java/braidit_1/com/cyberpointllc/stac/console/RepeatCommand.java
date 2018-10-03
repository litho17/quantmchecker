package braidit_1.com.cyberpointllc.stac.console;

import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.IOException;
import java.io.PrintStream;
import java.util.List;

public class RepeatCommand extends Command {
    private static final String NAME = "repeat";
    private static final int MAX_REPEATS = 5;
    private Display display;

    public RepeatCommand(Display display) {
        super(NAME, "Repeats the last n commands", "repeat <number of commands to repeat>");
        this.display = display;
    }

    @Override
    @Summary({"this.display.history", "cmdLine.args"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() != 1) {
            out.println(this.fetchUsage());
            return;
        }
        try {
            int numOfCommandsToRepeat = Integer.parseInt(cmdLine.getArgList().get(0));
            if (numOfCommandsToRepeat > MAX_REPEATS) {
                out.println("Error cannot perform more than " + MAX_REPEATS + " repeats.");
                return;
            }
            int size = display.history().size();

            // we need size - 1 because the most recent repeat command is in the
            // history, but we do not count it
            if (size - 1 < numOfCommandsToRepeat) {
                out.println("Error: cannot repeat " + numOfCommandsToRepeat + " commands when only " + (size - 1)
                        + " have been executed");
            } else if (numOfCommandsToRepeat > 0) {
                for (int q = size - numOfCommandsToRepeat - 1; q < size - 1; q++) {
                    executeAdviser(out, display.history().get(q));
                }
            }
        } catch (NumberFormatException e) {
            out.println(this.fetchUsage());
        } catch (IOException e) {
            out.println(e.getMessage());
        }
    }

    @Summary({"this.display.history", "1"})
    private void executeAdviser(PrintStream out, String command1) throws IOException {
        String command = command1;
        // print command so user can see what command is being executed
        out.println(command);

        // check that we are not repeating the repeat command
        String[] commandArgs = command.split(" ");
        if (!commandArgs[0].equalsIgnoreCase(NAME)) {
            display.executeCommand(command, false);
        } else {
            out.println("Cannot repeat a repeat command");
        }
    }
}