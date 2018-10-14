package SnapBuddy_1.com.cyberpointllc.stac.console;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

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
        int conditionObj0 = 1;
        if (cmdLine.getArgList().size() != conditionObj0) {
            out.println(this.getUsage());
            return;
        }
        int conditionObj1 = 0;
        try {
            int numOfCommandsToRepeat = Integer.parseInt(cmdLine.getArgList().get(0));
            if (numOfCommandsToRepeat > MAX_REPEATS) {
                out.println("Error cannot perform more than " + MAX_REPEATS + " repeats.");
                return;
            }

            @Bound("console.history") int j;
            @Inv("= (- history it) (- c31 c30)") List<String> history = new ArrayList<>();
            @Iter("<= it console.history") Iterator<String> it = console.history.iterator();
            while (it.hasNext()) {
                String s;
                c30: s = it.next();
                c31: history.add(s);
            }


            int size = history.size();
            // history, but we do not count it
            if (size - 1 < numOfCommandsToRepeat) {
                out.println("Error: cannot repeat " + numOfCommandsToRepeat + " commands when only " + (size - 1) + " have been executed");
            } else if (numOfCommandsToRepeat > conditionObj1) {
                for (int i = size - numOfCommandsToRepeat - 1; i < size - 1; i++) {
                    String command = history.get(i);
                    // print command so user can see what command is being executed
                    out.println(command);
                    // check that we are not repeating the repeat command
                    String[] commandArgs = command.split(" ");
                    if (!commandArgs[0].equalsIgnoreCase(NAME)) {
                        console.executeCommand(command, false);
                    } else {
                        executeHelper(out);
                    }
                }
            }
        } catch (NumberFormatException e) {
            out.println(this.getUsage());
        } catch (IOException e) {
            out.println(e.getMessage());
        }
    }

    private void executeHelper(PrintStream out) throws IOException, NumberFormatException {
        out.println("Cannot repeat a repeat command");
    }
}
