package battleboats_1.com.cyberpointllc.stac.command;

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
        if (cmdLine.getArgList().size() > 0) {
            for (int b = 0; b < cmdLine.getArgList().size(); b++) {
                String cmdName = cmdLine.getArgList().get(b);
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
        @Bound("+ console.permanentCommands console.currentCommands") int j;
        @Inv("= (- commands it1 it2) (- (+ c129 c134) c128 c133)") List<Command> commands = new ArrayList<>();
        @Iter("<= it1 console.currentCommands") Iterator<Command> it1 = console.currentCommands.values().iterator();
        Command c;
        while (it1.hasNext()) {
            c128: c = it1.next();
            c129: commands.add(c);
        }
        @Iter("<= it2 console.permanentCommands")Iterator<Command> it2 = console.permanentCommands.values().iterator();
        while (it2.hasNext()) {
            c133: c = it2.next();
            c134: commands.add(c);
        }
        
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
