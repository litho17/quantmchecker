package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.Pin;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

public class RandomlyDefineBoardCommand extends Command {
    private static final String COMMAND = "place_all";
    private static final String USAGE = COMMAND + " <seed>";
    private static final String[] DIRECTIONS = {"up", "down", "left", "right"};

    private final WarShips warShips;

    public RandomlyDefineBoardCommand(WarShips warShips) {
        super(COMMAND, "Place all your boats and opponent's cannon randomly on board", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {

        if ((warShips.pullStage() != Stage.LAY_SHIPS) && (warShips.pullStage() != Stage.LAY_SHIPS_AND_FINISH)) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + warShips.pullStage());
        } else {
            if (cmdLine.getArgList().size() != 1) {
                warShips.printUsrMsg(USAGE);
            } else {
                executeService(cmdLine.getArgList());
            }
        }
    }

    private void executeService(List<String> argList) {
        try {
            long seed = Long.parseLong(argList.get(0));
            layAllRandomly(seed);
            warShips.assignStage(Stage.LAY_SHIPS_AND_FINISH);
            warShips.printUsrMsg("Boats and cannon have all been randomly placed");
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }

    public void layAllRandomly(Long seed) {
        Random random = new Random(seed);
        @Bound("+ 1 Pin.SHIPS") int j;
        @Inv("= (- shipsAndCannon i) (- (+ c62 c65) c63)") Set<Pin> shipsAndCannon = new HashSet<>();
        for (@Iter("<= i Pin.SHIPS") int i = 0; i < Pin.SHIPS.length;) {
            c62: shipsAndCannon.add(Pin.SHIPS[i]);
            c63: i = i + 1;
        }
        c65: shipsAndCannon.add(Pin.CANNON);

        shipsAndCannon.forEach(pin -> layRandomly(pin, random));
    }

    private void layRandomly(Pin pin, Random random) {
        int boardSize = warShips.pullBoardSize();
        String status = "";

        while (!"successful".equalsIgnoreCase(status)) {
            // values from 1 to boardSize (inclusive)
            int x = random.nextInt(boardSize) + 1;
            int y = random.nextInt(boardSize) + 1;

            if (pin.equals(Pin.CANNON)) {
                boolean success = warShips.setCannon(x, y);
                if (success) {
                    status = "Successful";
                    warShips.printUsrMsg("Cannon has been placed at (" + x + ", " + y + ")");
                }
            } else {
                String name = pin.takeName();
                int length = pin.getLength();
                int directionIndex = random.nextInt(DIRECTIONS.length); // index into DIRECTIONS
                String direction = DIRECTIONS[directionIndex];
                status = warShips.defineShip(name, length, x, y, direction);
            }
        }
    }
}
