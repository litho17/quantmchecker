package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;
import java.util.Objects;

public class LayShipCommand extends Command {
    private static final String COMMAND_PREFIX = "place_";
    private static final String USAGE = " <X coordinate> <Y coordinate> <up | down | left | right>";

    private final WarShips warShips;
    private final String name;
    private final int length;

    public LayShipCommand(WarShips warShips, String name, int length) {
        super(COMMAND_PREFIX, "Assign the location of the " + name.toLowerCase() +
                        " by giving an X and Y coordinate and a direction of up, down, left, or right",
                USAGE);

        if (length <= 0) {
            throw new IllegalArgumentException("Boat length must be positive: " + length);
        }

        this.warShips = Objects.requireNonNull(warShips, "BattleBoats may not be null");
        this.name = Objects.requireNonNull(name, "Name may not be null").trim();
        this.length = length;
    }

    @Override
    public String grabName() {
        return super.grabName() + name.toLowerCase();
    }

    @Override
    public String pullUsage() {
        return grabName() + super.pullUsage();
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if ((warShips.pullStage() != Stage.LAY_SHIPS) && (warShips.pullStage() != Stage.LAY_SHIPS_AND_FINISH)) {
            warShips.printUsrMsg("Command " + grabName() + " is illegal from " + warShips.pullStage());
        } else {
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 3) {
                    warShips.printUsrMsg(USAGE);
                } else {
                    executeFunction(argList);
                }
            } catch (Exception e) {
                warShips.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }
    }

    private void executeFunction(List<String> argList) {
        int x = Integer.parseInt(argList.get(0));
        int y = Integer.parseInt(argList.get(1));
        String direction = argList.get(2);
        String status = warShips.defineShip(name, length, x, y, direction);
        if ("successful".equalsIgnoreCase(status)) {
            warShips.printUsrMsg(name + " has been placed");
        } else {
            warShips.printUsrMsg("The " + name + " cannot be placed there: " + status);
        }

        if (warShips.areAllShipsPlaced()) {
            warShips.assignStage(Stage.LAY_SHIPS_AND_FINISH);
        }
    }
}
