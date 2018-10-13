package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class DisconnectCommand extends Command {
    private static final String COMMAND = "disconnect";
    private static final String USAGE = COMMAND;

    private final WarShips warShips;

    public DisconnectCommand(WarShips warShips) {
        super(COMMAND, "Disconnect from current connection", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {

        if (warShips.pullStage() == Stage.IDLE) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + warShips.pullStage());
        } else {
            executeGateKeeper(out, cmdLine);
        }
    }

    private void executeGateKeeper(PrintStream out, CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 0) {
                out.println(USAGE);
            } else {
                if (warShips.hasConnection()) {
                    warShips.disconnect();
                } else {
                    warShips.printUsrMsg("Cannot disconnect -- no connection exists");
                }
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }
}
