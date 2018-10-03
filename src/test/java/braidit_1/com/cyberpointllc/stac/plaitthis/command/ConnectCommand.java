package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.console.Command;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class ConnectCommand extends Command {
    private static final Logger logger = LoggerFactory.getLogger(ConnectCommand.class);
    private static final String COMMAND = "connect";
    private static final String USAGE = COMMAND + "<host> <port>";

    private final PlaitIt plaitIt;

    public ConnectCommand(PlaitIt plaitIt) {
        super(COMMAND, "request connection with user at specified host and port", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.IDLE)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else {
            executeUtility(out, cmdLine);
        }
    }

    private void executeUtility(PrintStream out, CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 2) {
                out.println(USAGE);
            } else {
                logger.info("Connecting to {}:{}", cmdLine.getArgList().get(0), cmdLine.getArgList().get(1));
                if (!plaitIt.hasConnection()) {
                    plaitIt.connect(cmdLine.getArgList().get(0), Integer.parseInt(cmdLine.getArgList().get(1)));
                } else {
                    plaitIt.printUsrMsg("Cannot connect to another user while connected");
                }
            }
        } catch (Exception e) {
            plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }
}
