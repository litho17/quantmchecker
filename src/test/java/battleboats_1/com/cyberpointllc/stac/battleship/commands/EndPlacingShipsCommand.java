package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class EndPlacingShipsCommand extends Command {
    private static final String COMMAND = "end_placing_boats";
    private static final String USAGE = COMMAND;

    private final WarShips warShips;

    public EndPlacingShipsCommand(WarShips warShips) {
        super(COMMAND, "Indicate you are done placing your boats and cannon on your Ocean Board", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {

        if (warShips.pullStage() != Stage.LAY_SHIPS_AND_FINISH) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal from " + warShips.pullStage() + ".  Try to connect first.");
        } else {
            try {
                if (cmdLine.getArgList().size() != 0) {
                    warShips.printUsrMsg(USAGE);
                } else {
                    executeEntity();
                }

            } catch (Exception e) {
                warShips.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }

    }

    private void executeEntity() throws TalkersDeviation {
        BattleBoatsMessage message = BattleBoatsMessage.newBuilder()
                .setType(Type.BOATS_PLACED)
                .setReadyMsg(warShips.rarefy(warShips.getPlacementMessage()))
                .build();
        warShips.sendMessage(message.toByteArray());

        warShips.printUsrMsg("Done placing your boats");
        warShips.defineUpCompetition();
        if (warShips.amIFirst()) {
            warShips.assignStage(Stage.IM_READY);
        } else {
            warShips.assignStage(Stage.WAIT_FOR_FIRE);
        }
    }
}
