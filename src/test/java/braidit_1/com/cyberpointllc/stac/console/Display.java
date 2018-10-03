package braidit_1.com.cyberpointllc.stac.console;

import jline.console.ConsoleReader;
import jline.console.CursorBuffer;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.*;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.*;

public class Display {
    private final PrintStream out;
    private final ConsoleReader reader;
    private List<String> history = new ArrayList<String>();

    // commands that are available in the current program state
    private final Map<String, Command> currentCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
    // commands that a user can use at any time
    private final Map<String, Command> permanentCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
    // commands that might become available in the future
    private final Map<String, Command> inactiveCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

    private final CommandLineParser commandLineParser = new DefaultParser();

    private boolean shouldExit = false;
    private LineManager defaultLineManager = null;
    private CursorBuffer stashed;

    public Display(String name) throws IOException {
        this(name, System.in, System.out);
    }

    public Display(String name, InputStream inputStream, PrintStream out) throws IOException {
        this(name, inputStream, out, false, false);
    }

    @Summary({"this.addPermanentCommand", "5"})
    public Display(String name, InputStream inputStream, PrintStream out, boolean includeRepeat, boolean includeScript) throws IOException {
        if (StringUtils.isBlank(name)) {
            throw new IllegalArgumentException("Console name may not be null");
        }

        if (inputStream == null) {
            throw new IllegalArgumentException("InputStream may not be null");
        }

        if (out == null) {
            throw new IllegalArgumentException("PrintStream may not be null");
        }

        this.out = out;

        reader = new ConsoleReader(inputStream, out);
        reader.setPrompt(name + "> ");
        reader.addCompleter(new CommandCompleterBuilder().defineDisplay(this).composeCommandCompleter());

        c70: addPermanentCommand(new ExitCommand(this));
        c71: addPermanentCommand(new HelpCommand(this));

        c73: addPermanentCommand(new HistoryCommand(this));
        if (includeRepeat) {
            c75: addPermanentCommand(new RepeatCommand(this));
        }
        if (includeScript) {
            c78: addPermanentCommand(new ScriptCommandBuilder().defineDisplay(this).composeScriptCommand());
        }
    }

    @Summary({"this.permanentCommands", "1"})
    public void addPermanentCommand(Command command) {
        if (command == null) {
            throw new IllegalArgumentException("Command may not be null");
        }

        permanentCommands.put(command.takeName(), command);

        if (command.grabCompleter() != null) {
            reader.addCompleter(command.grabCompleter());
        }
    }

    @Summary({"this.inactiveCommands", "1"})
    public void addInactiveCommand(Command command){
        if (command == null) {
            throw new IllegalArgumentException("Command may not be null");
        }
        inactiveCommands.put(command.takeName(), command);
        if (command.grabCompleter() != null) {
            reader.addCompleter(command.grabCompleter());
        }
    }

    @Summary({"this.currentCommands", "1"})
    public void activateCommand(String cmd){
        Command command = inactiveCommands.get(cmd);
        if (command == null) {
            throw new IllegalArgumentException("Command " + cmd + " not found");
        }
        currentCommands.put(cmd, command);
    }

    public void renewCurrentCommands(){
        for (Command command : currentCommands.values()){
            reader.removeCompleter(command.grabCompleter());
        }
        currentCommands.clear();
    }

    public void defineDefaultLineCoordinator(LineManager manager) {
        this.defaultLineManager = manager;
    }

    /**
     * @return a copy of the commands
     */
    public List<Command> obtainCommands() {
        @Bound("+ currentCommands permanentCommands") int i;
        @Inv("= (- commands it1 it2) (- (+ c133 c138) c132 c137)") List<Command> commands = new ArrayList<>();
        @Iter("<= it1 currentCommands") Iterator<Command> it1 = currentCommands.values().iterator();
        Command c;
        while (it1.hasNext()) {
            c132: c = it1.next();
            c133: commands.add(c);
        }
        @Iter("<= it2 permanentCommands") Iterator<Command> it2 = permanentCommands.values().iterator();
        while (it2.hasNext()) {
            c137: c = it2.next();
            c138: commands.add(c);
        }
        return commands;
    }

    public boolean hasCommand(String name) {
        return currentCommands.containsKey(name) || permanentCommands.containsKey(name);
    }

    public Command getCommand(String name) {
        if (currentCommands.containsKey(name)) {
            return currentCommands.get(name);
        } else {
            return permanentCommands.get(name);
        }
    }

    public String pullEnsuingCommand() throws IOException {
        return reader.readLine();
    }

    /**
     * Convenience routine that runs by executing each subsequent command until
     * directed to exit.
     */
    public void execute() throws IOException {
        while (!shouldExit()) {
            executeEnsuingCommand();
        }
    }

    /**
     * Executes the next command entered by the user
     *
     * @throws IOException
     */
    public void executeEnsuingCommand() throws IOException {
        executeCommand(reader.readLine());
    }


    /**
     * Executes the command passed in
     *
     * @param line the command and parameters to execute
     * @throws IOException
     */
    @Summary({"this.history", "1"})
    public void executeCommand(String line) throws IOException {
        executeCommand(line, true);
    }

    /**
     * Executes the command passed in
     *
     * @param line         the command and parameters to execute
     * @param addToHistory indicates if the line should be added to history
     * @throws IOException
     */
    @Summary({"this.history", "1"})
    public void executeCommand(String line, boolean addToHistory) throws IOException {
        if (line == null) {
            // end of file? must have been a console redirect
            // we need to exit no matter what.
            setShouldExit(true);
            return;
        }

        // split the line by spaces, the first item is the command
        String[] items = line.split(" ");
        if (items.length == 0) {
            // no op
            return;
        }

        String name = items[0];

        if (StringUtils.isEmpty(name)) {
            // no op
            return;
        }

        if (hasCommand(name)) {
            Command command = getCommand(name);
            try {
                boolean stopAtNonOption = command.takeOptions().getOptions().isEmpty();
                CommandLine cmdLine = commandLineParser.parse(command.takeOptions(),
                        Arrays.copyOfRange(items, 1, items.length), stopAtNonOption);
                // add command to command history
                if (addToHistory) {
                    history.add(line);
                }
                command.execute(out, cmdLine);

            } catch (ParseException e) {
                out.print("Error: " + e.getMessage());
            }
        } else if (defaultLineManager == null) {
            out.println("Invalid command: '" + name + "'");
        } else {
            defaultLineManager.handleLine(line, out);
        }
    }

    public void setShouldExit(boolean shouldExit) {
        this.shouldExit = shouldExit;
    }

    public boolean shouldExit() {
        return shouldExit;
    }

    /**
     * Takes in a file who has a command on each line and executes those
     * commands
     *
     * @param file
     */
    @Summary({"this.history", "1"})
    public void runScript(File file) throws Exception {
        BufferedReader reader = new BufferedReader(new FileReader(file));
        String read = reader.readLine();
        while (read != null) {
            read = read.trim();
            // don't execute the line if the line is empty or is a comment
            if (!read.isEmpty() && read.charAt(0) != '#') {
                String[] commandArgs = read.split(" ");
                // don't execute script commands from scripts
                if (!commandArgs[0].equalsIgnoreCase(ScriptCommand.NAME)) {
                    // print the command so the user knows what is being executed
                    System.out.println(read);
                    this.executeCommand(read);
                }
            }
            read = reader.readLine();
        }
    }

    /**
     * @return a copy of the command history
     */
    public List<String> history() {
        return new ArrayList<String>(history);
    }

    /**
     * Redraws the console line
     */
    public void redrawDisplay() throws IOException {
        reader.drawLine();
        reader.flush();
    }

    // from http://stackoverflow.com/questions/9010099/jline-keep-prompt-at-the-bottom
    public void stashLine() {
        stashed = reader.getCursorBuffer().copy();
        try {
            reader.getOutput().write("\u001b[1G\u001b[K");
            reader.flush();
        } catch (IOException e) {
            // ignore
        }
    }

    public void unstashLine() {
        try {
            reader.resetPromptLine(this.reader.getPrompt(),
                    this.stashed.toString(), this.stashed.cursor);
        } catch (IOException e) {
            // ignore
        }
    }

    public PrintStream getOutputStream() {
        return out;
    }
}
