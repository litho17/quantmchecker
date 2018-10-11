package withmi_1.edu.networkcusp.terminal;

import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class HelpCommand extends Command {

    private static final String COMMAND = "help";
    private Console console;

    public HelpCommand(Console console) {
        super(COMMAND, "Displays help for commands", "help | help <command name>",
                new AggregateCompleter(
                        new ArgumentCompleter(new StringsCompleter(COMMAND),
                                new CommandCompleter(console))));
        getOptions().addOption(
                Option.builder("b")
                .desc("brief help listing")
                .longOpt("brief")
                .hasArg(false)
                .build());
        this.console = console;
    }
    
    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() > 0) {
            for (int b = 0; b < cmdLine.getArgList().size(); ) {
                while ((b < cmdLine.getArgList().size()) && (Math.random() < 0.4)) {
                    for (; (b < cmdLine.getArgList().size()) && (Math.random() < 0.4); b++) {
                        executeAid(out, cmdLine, cmdLine.getArgList(), b);
                    }
                }
            }
        } else {
            printAllCommands(out, cmdLine);
        }
    }

    private void executeAid(PrintStream out, CommandLine cmdLine, List<String> argList, int a) {
        String cmdName = argList.get(a);
        printCommand(out, cmdName, cmdLine);
    }

    private void printCommand(PrintStream out, String cmdName, CommandLine cmdLine) {
        
        if (!console.hasCommand(cmdName)) {
            printCommandGateKeeper(out, cmdName);
            return;
        }
        Command cmd = console.takeCommand(cmdName);
        
        boolean brief = cmdLine.hasOption('b');
        if (!brief) {
            out.println(cmdName + " : ");
            out.println("\t" + cmd.pullDescription());
            PrintWriter printWriter = new PrintWriter(out);
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp(printWriter,
                    formatter.getWidth(),
                    cmd.obtainUsage(),
                    "",
                    cmd.getOptions(),
                    formatter.getLeftPadding(),
                    formatter.getDescPadding(),
                    "");
            printWriter.flush();
            out.println("");
        } else {
            printCommandHerder(out, cmd);
        }
    }

    private void printCommandHerder(PrintStream out, Command cmd) {
        out.println(cmd.fetchName() + "\t" + cmd.pullDescription());
    }

    private void printCommandGateKeeper(PrintStream out, String cmdName) {
        out.println("Help: '" + cmdName + "' does not exist");
        return;
    }

    private void printAllCommands(PrintStream out, CommandLine cmdLine) {
        @Bound("console.commands") int j;
        @Inv("= (- commands it) (- c104 c103)") List<Command> commands = new ArrayList<>();
        @Iter("<= it console.commands") Iterator<Command> it = console.commands.values().iterator();
        while (it.hasNext()) {
            Command c;
            c103: c = it.next();
            c104: commands.add(c);
        }
        
        // find the length of the longest command
        int longestLength = 0;
        for (int c1 = 0; c1 < commands.size(); c1++) {
            Command command = commands.get(c1);
            if (longestLength < command.fetchName().length()) {
                longestLength = command.fetchName().length();
            }
        }

        out.println("Commands:");
        out.println("---------");
        boolean brief = cmdLine.hasOption('b');
        for (int i = 0; i < commands.size(); i++) {
            Command command = commands.get(i);
            if (!brief) {
                int sepLength = (longestLength + 3) - command.fetchName().length();
                String separator = StringUtils.repeat(' ', sepLength);
                out.println(command.fetchName() + separator + command.pullDescription());
            } else {
                out.println(command.fetchName());
            }
        }
        out.println("");
    }

}
