package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class LayCannonCommand extends Command {
    private static final String COMMAND = "place_cannon";
    private static final String USAGE = COMMAND + " <X coordinate> <Y coordinate>";

    private final WarShips warShips;

    public LayCannonCommand(WarShips warShips) {
        super(COMMAND, "Assign the location of the opponent's cannon by giving an X and Y coordinate", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if ((stage != Stage.LAY_SHIPS) && (stage != Stage.LAY_SHIPS_AND_FINISH)) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            executeExecutor(cmdLine);
        }
    }

    private void executeExecutor(CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 2) {
                warShips.printUsrMsg(USAGE);
            } else {
                executeExecutorManager(cmdLine.getArgList());
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }

    private void executeExecutorManager(List<String> argList) {
        int x = Integer.parseInt(argList.get(0));
        int y = Integer.parseInt(argList.get(1));
        boolean isPlaced = warShips.setCannon(x, y);
        if (isPlaced) {
            warShips.printUsrMsg("Cannon has been placed.");
        } else {
            warShips.printUsrMsg("Cannon cannot be placed at (" + x + ", " + y + ").");
        }

        if (warShips.areAllShipsPlaced()) {
            warShips.assignStage(Stage.LAY_SHIPS_AND_FINISH);
        }
    }
}
