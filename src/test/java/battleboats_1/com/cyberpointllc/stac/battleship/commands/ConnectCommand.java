package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class ConnectCommand extends Command {
    private static final String COMMAND = "connect";
    private static final String USAGE = COMMAND + "<host> <port>";

    private final WarShips warShips;

    public ConnectCommand(WarShips warShips) {
        super(COMMAND, "Request a connection with the user at the specified host and port", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (warShips.pullStage() != Stage.IDLE) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + warShips.pullStage());
        } else {
            executeHerder(out, cmdLine);
        }
    }

    private void executeHerder(PrintStream out, CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 2) {
                out.println(USAGE);
            } else {
                if (!warShips.hasConnection()) {
                    warShips.connect(cmdLine.getArgList().get(0), Integer.parseInt(cmdLine.getArgList().get(1)));
                } else {
                    warShips.printUsrMsg("Cannot connect to another user while connected");
                }
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }
}
