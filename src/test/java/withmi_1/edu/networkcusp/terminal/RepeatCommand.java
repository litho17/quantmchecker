package withmi_1.edu.networkcusp.terminal;

import org.apache.commons.cli.CommandLine;

import java.io.IOException;
import java.io.PrintStream;
import java.util.List;

public class RepeatCommand extends Command {
    private static final String NAME = "repeat";
    private static final int MAX_REPEATS = 5;
    private Console console;

    public RepeatCommand(Console console) {
        super(NAME, "Repeats the last n commands", "repeat <number of commands to repeat>");
        this.console = console;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() != 1) {
            executeAssist(out);
            return;
        }
        try {
            int numOfCommandsToRepeat = Integer.parseInt(cmdLine.getArgList().get(0));
            if (numOfCommandsToRepeat > MAX_REPEATS) {
                out.println("Error cannot perform more than " + MAX_REPEATS + " repeats.");
                return;
            }
            int size = console.history().size();

            // we need size - 1 because the most recent repeat command is in the
            // history, but we do not count it
            if (size - 1 < numOfCommandsToRepeat) {
                out.println("Error: cannot repeat " + numOfCommandsToRepeat + " commands when only " + (size - 1)
                        + " have been executed");
            } else if (numOfCommandsToRepeat > 0) {
                for (int k = size - numOfCommandsToRepeat - 1; k < size - 1; k++) {
                    executeEntity(out, console.history(), k);
                }
            }
        } catch (NumberFormatException e) {
            out.println(this.obtainUsage());
        } catch (IOException e) {
            out.println(e.getMessage());
        }
    }

    private void executeEntity(PrintStream out, List<String> history, int b) throws IOException {
        String command = history.get(b);
        // print command so user can see what command is being executed
        out.println(command);

        // check that we are not repeating the repeat command
        String[] commandArgs = command.split(" ");
        if (!commandArgs[0].equalsIgnoreCase(NAME)) {
            console.executeCommand(command, false);
        } else {
            executeEntitySupervisor(out);
        }
    }

    private void executeEntitySupervisor(PrintStream out) {
        out.println("Cannot repeat a repeat command");
    }

    private void executeAssist(PrintStream out) {
        out.println(this.obtainUsage());
        return;
    }
}