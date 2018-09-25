package braidit_1.com.cyberpointllc.stac.console;

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
    private Display display;

    public HelpCommand(Display display) {
        super(COMMAND, "Displays help for commands", "help | help <command name>",
                new AggregateCompleter(
                        new ArgumentCompleter(new StringsCompleter(COMMAND),
                                new CommandCompleterBuilder().defineDisplay(display).composeCommandCompleter())));
        takeOptions().addOption(
                Option.builder("b")
                .desc("brief help listing")
                .longOpt("brief")
                .hasArg(false)
                .build());
        this.display = display;
    }
    
    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        List<String> argList = cmdLine.getArgList();
        if (argList.size() > 0) {
            for (int i = 0; i < argList.size(); i++) {
                String cmdName = argList.get(i);
                printCommand(out, cmdName, cmdLine);
            }
        } else {
            printAllCommands(out, cmdLine);
        }
    }

    private void printCommand(PrintStream out, String cmdName, CommandLine cmdLine) {
        
        if (!display.hasCommand(cmdName)) {
            out.println("Help: '" + cmdName + "' does not exist");
            return;
        }
        Command cmd = display.getCommand(cmdName);
        
        boolean brief = cmdLine.hasOption('b');
        if (!brief) {
            out.println(cmdName + " : ");
            out.println("\t" + cmd.pullDescription());
            PrintWriter printWriter = new PrintWriter(out);
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp(printWriter,
                    formatter.getWidth(),
                    cmd.fetchUsage(),
                    "",
                    cmd.takeOptions(),
                    formatter.getLeftPadding(),
                    formatter.getDescPadding(),
                    "");
            printWriter.flush();
            out.println("");
        } else {
            out.println(cmd.takeName() + "\t" + cmd.pullDescription());
        }
    }
    
    private void printAllCommands(PrintStream out, CommandLine cmdLine) {
        List<Command> commands = display.obtainCommands();
        
        // find the length of the longest command
        int longestLength = 0;
        for (int b = 0; b < commands.size(); b++) {
            Command command = commands.get(b);
            if (longestLength < command.takeName().length()) {
                longestLength = command.takeName().length();
            }
        }

        out.println("Commands:");
        out.println("---------");
        boolean brief = cmdLine.hasOption('b');
        for (int p = 0; p < commands.size(); p++) {
            Command command = commands.get(p);
            if (!brief) {
                int sepLength = (longestLength + 3) - command.takeName().length();
                String separator = StringUtils.repeat(' ', sepLength);
                out.println(command.takeName() + separator + command.pullDescription());
            } else {
                out.println(command.takeName());
            }
        }
        out.println("");
    }

}
