package battleboats_1.com.cyberpointllc.stac.command;

import jline.console.ConsoleReader;
import jline.console.CursorBuffer;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;
import org.apache.commons.lang3.StringUtils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

public class Console {
    private final PrintStream out;
    private final ConsoleReader reader;
    private List<String> history = new ArrayList<String>();

    // commands that are available in the current program state
    private final Map<String, Command> currentCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
    // commands that a user can use at any time
    private final Map<String, Command> permanentCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
    // commands that might become available in the future
    private final Map<String, Command> inactiveCommands = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

    private final CommandLineParser commandLineGrabber = new DefaultParser();

    private boolean shouldExit = false;
    private LineManager defaultLineManager = null;
    private CursorBuffer stashed;

    public Console(String name) throws IOException {
        this(name, System.in, System.out);
    }

    public Console(String name, InputStream inputStream, PrintStream out) throws IOException {
        this(name, inputStream, out, false, false);
    }

    public Console(String name, InputStream inputStream, PrintStream out, boolean includeRepeat, boolean includeScript) throws IOException {
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
        reader.addCompleter(new CommandCompleter(this));

        addPermanentCommand(new ExitCommand(this));
        addPermanentCommand(new HelpCommand(this));

        addPermanentCommand(new HistoryCommandProducer().assignConsole(this).makeHistoryCommand());
        if (includeRepeat) {
            addPermanentCommand(new RepeatCommand(this));
        }
        if (includeScript) {
            addPermanentCommand(new ScriptCommand(this));
        }
    }

    public void addPermanentCommand(Command command) {
        if (command == null) {
            throw new IllegalArgumentException("Command may not be null");
        }

        permanentCommands.put(command.grabName(), command);

        if (command.fetchCompleter() != null) {
            reader.addCompleter(command.fetchCompleter());
        }
    }

    public void addInactiveCommand(Command command){
        if (command == null) {
            throw new IllegalArgumentException("Command may not be null");
        }
        inactiveCommands.put(command.grabName(), command);
        if (command.fetchCompleter() != null) {
            reader.addCompleter(command.fetchCompleter());
        }
    }

    public void activateCommand(String cmd){
        Command command = inactiveCommands.get(cmd);
        if (command == null) {
            throw new IllegalArgumentException("Command " + cmd + " not found");
        }
        currentCommands.put(cmd, command);
    }

    public void releaseCurrentCommands(){
        for (Command command : currentCommands.values()){
            reader.removeCompleter(command.fetchCompleter());
        }
        currentCommands.clear();
    }

    public void fixDefaultLineManager(LineManager manager) {
        this.defaultLineManager = manager;
    }

    /**
     * @return a copy of the commands
     */
    public List<Command> pullCommands() {
        List<Command> commands = new ArrayList<>();
        commands.addAll(currentCommands.values());
        commands.addAll(permanentCommands.values());
        return commands;
    }

    public boolean hasCommand(String name) {
        return currentCommands.containsKey(name) || permanentCommands.containsKey(name);
    }

    public Command obtainCommand(String name) {
        if (currentCommands.containsKey(name)) {
            return currentCommands.get(name);
        } else {
            return permanentCommands.get(name);
        }
    }

    public String grabFollowingCommand() throws IOException {
        return reader.readLine();
    }

    /**
     * Convenience routine that runs by executing each subsequent command until
     * directed to exit.
     */
    public void execute() throws IOException {
        while (!shouldExit()) {
            executeFollowingCommand();
        }
    }

    /**
     * Executes the next command entered by the user
     *
     * @throws IOException
     */
    public void executeFollowingCommand() throws IOException {
        executeCommand(reader.readLine());
    }


    /**
     * Executes the command passed in
     *
     * @param line the command and parameters to execute
     * @throws IOException
     */
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
    public void executeCommand(String line, boolean addToHistory) throws IOException {
        if (line == null) {
            // end of file? must have been a console redirect
            // we need to exit no matter what.
            defineShouldExit(true);
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
            Command command = obtainCommand(name);
            try {
                boolean stopAtNonOption = command.obtainOptions().getOptions().isEmpty();
                CommandLine cmdLine = commandLineGrabber.parse(command.obtainOptions(),
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

    public void defineShouldExit(boolean shouldExit) {
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
    public void runScript(File file) throws Exception {
        BufferedReader reader = new BufferedReader(new FileReader(file));
        String read = reader.readLine();
        while (read != null) {
            read = read.trim();
            // don't execute the line if the line is empty or is a comment
            if (!read.isEmpty() && read.charAt(0) != '#') {
                runScriptGuide(read);
            }
            read = reader.readLine();
        }
    }

    private void runScriptGuide(String read) throws IOException {
        String[] commandArgs = read.split(" ");
        // don't execute script commands from scripts
        if (!commandArgs[0].equalsIgnoreCase(ScriptCommand.NAME)) {
            // print the command so the user knows what is being executed
            runScriptGuideFunction(read);
        }
    }

    private void runScriptGuideFunction(String read) throws IOException {
        System.out.println(read);
        this.executeCommand(read);
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
    public void redrawConsole() throws IOException {
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

    public PrintStream obtainOutputStream() {
        return out;
    }
}
