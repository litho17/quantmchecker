package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.ShotMadeMessage;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;
import java.util.Objects;

public class DeclareFireCommand extends Command {
    private static final String COMMAND = "shoot";
    private static final String USAGE = COMMAND + " <height in meters> <velocity in m/s> <elevation_angle in degrees, zero being horizontal> <board_angle in degrees, zero being to the right and increasing counter clockwise>";

    private final WarShips warShips;

    public DeclareFireCommand(WarShips warShips) {
        super(COMMAND, "Declare a shot by giving a height, velocity, elevation angle, and board angle", USAGE);
        this.warShips = Objects.requireNonNull(warShips, "BattleBoats may not be null");
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if (stage != Stage.DECLARE_FIRE) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 4) {
                    warShips.printUsrMsg(USAGE);
                } else {
                    String height = argList.get(0);
                    String speed = argList.get(1);
                    String elevationAngle = argList.get(2); // degrees
                    String boardAngle = argList.get(3); // degrees

                    ShotMadeMessage message = ShotMadeMessage.newBuilder()
                            .setHeight(height)
                            .setVelocity(speed)
                            .setVerticalAngle(elevationAngle)
                            .setBoardAngle(boardAngle)
                            .build();
                    BattleBoatsMessage msg = BattleBoatsMessage.newBuilder()
                            .setType(Type.SHOT_MADE)
                            .setShotMsg(message)
                            .build();
                    warShips.sendMessage(msg.toByteArray());

                    warShips.assignStage(Stage.WAIT_FOR_REPORT);
                }
            } catch (Exception e) {
                warShips.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }
    }
}
