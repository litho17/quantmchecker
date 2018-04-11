package battleboats_1.com.cyberpointllc.stac.command;

import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.lang3.StringUtils;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.List;

public class HelpCommand extends Command {

    private static final String COMMAND = "help";
    private Console console;

    public HelpCommand(Console console) {
        super(COMMAND, "Displays help for commands", "help | help <command name>",
                new AggregateCompleter(
                        new ArgumentCompleter(new StringsCompleter(COMMAND),
                                new CommandCompleter(console))));
        obtainOptions().addOption(
                Option.builder("b")
                .desc("brief help listing")
                .longOpt("brief")
                .hasArg(false)
                .build());
        this.console = console;
    }
    
    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        List<String> argList = cmdLine.getArgList();
        if (argList.size() > 0) {
            for (int b = 0; b < argList.size(); b++) {
                String cmdName = argList.get(b);
                printCommand(out, cmdName, cmdLine);
            }
        } else {
            printAllCommands(out, cmdLine);
        }
    }

    private void printCommand(PrintStream out, String cmdName, CommandLine cmdLine) {
        
        if (!console.hasCommand(cmdName)) {
            out.println("Help: '" + cmdName + "' does not exist");
            return;
        }
        Command cmd = console.obtainCommand(cmdName);
        
        boolean brief = cmdLine.hasOption('b');
        if (!brief) {
            out.println(cmdName + " : ");
            out.println("\t" + cmd.fetchDescription());
            PrintWriter printWriter = new PrintWriter(out);
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp(printWriter,
                    formatter.getWidth(),
                    cmd.pullUsage(),
                    "",
                    cmd.obtainOptions(),
                    formatter.getLeftPadding(),
                    formatter.getDescPadding(),
                    "");
            printWriter.flush();
            out.println("");
        } else {
            out.println(cmd.grabName() + "\t" + cmd.fetchDescription());
        }
    }
    
    private void printAllCommands(PrintStream out, CommandLine cmdLine) {
        List<Command> commands = console.pullCommands();
        
        // find the length of the longest command
        int longestLength = 0;
        for (int i = 0; i < commands.size(); i++) {
            Command command = commands.get(i);
            if (longestLength < command.grabName().length()) {
                longestLength = command.grabName().length();
            }
        }

        out.println("Commands:");
        out.println("---------");
        boolean brief = cmdLine.hasOption('b');
        for (int k = 0; k < commands.size(); k++) {
            Command command = commands.get(k);
            if (!brief) {
                int sepLength = (longestLength + 3) - command.grabName().length();
                String separator = StringUtils.repeat(' ', sepLength);
                out.println(command.grabName() + separator + command.fetchDescription());
            } else {
                out.println(command.grabName());
            }
        }
        out.println("");
    }

}
