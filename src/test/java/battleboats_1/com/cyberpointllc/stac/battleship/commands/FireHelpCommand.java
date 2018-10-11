package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class FireHelpCommand extends Command {
    private static final String COMMAND = "shot_help";
    private static final String USAGE = COMMAND + " <x coordinate> <y coordinate>";
    private static final double G = 9.8; // Gravitational constant m/sec^2

    private final WarShips warShips;

    public FireHelpCommand(WarShips warShips) {
        super(COMMAND, "Given an x and a y coordinate on your radar board, provide a helpful shot hint", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if (stage != Stage.DECLARE_FIRE) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            List<String> argList = cmdLine.getArgList();
            if (argList.size() != 2) {
                warShips.printUsrMsg(USAGE);
            } else {
                try {
                    double x = Double.parseDouble(argList.get(0));
                    double y = Double.parseDouble(argList.get(1));
                    warShips.printUsrMsg(calculateParametersToStrike(x, y));
                } catch (Exception e) {
                    warShips.printUsrMsg("Problem processing command: " + e.getMessage());
                }
            }
        }
    }

    /**
     * Provide a set of shot parameters that will allow user
     * to hit the square (x, y) from (0, 0).
     * We use a height of 1 and a vertical angle of 45 degrees.
     */
    private String calculateParametersToStrike(double x, double y) {
        // (0, 0) special case
        if (x == 0 && y == 0) {
            return "1 1 90 0";
        }

        double initialSpeed = calculateInitialSpeed(x, y);
        double boardAngle = calculateBoardAngle(x, y);
        return "1 " + initialSpeed + " 45 " + boardAngle;
    }

    public double calculateInitialSpeed(double x, double y) {
        // Assumes h_0 = 1 and elevation of 45 degrees
        double h0 = 1; // This should work even if we change h0 (but would also have to change it above in the string, the unit test, and the memTest expect script that parses it)

        double s = warShips.pullSquareSize();
        double d = Math.sqrt((s * x * s * x) + (s * y * s * y)); // distance shot must travel
        double v0Squared = G * d * d / (d + h0);
        return Math.sqrt(v0Squared);
    }

    public double calculateBoardAngle(double x, double y) {
        double angleRadians = Math.atan2(y, x); // this is in the range [-pi, pi]
        // adjust the quadrant if necessary
        while (angleRadians < 0) {
            angleRadians += (2 * Math.PI);
        }
        return angleRadians * 180 / Math.PI;
    }
}
