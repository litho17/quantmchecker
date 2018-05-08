package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class DeclineCompetitionCommand extends Command {
    private static final String COMMAND = "decline_game";
    private static final String USAGE = COMMAND;

    private final WarShips warShips;

    public DeclineCompetitionCommand(WarShips warShips) {
        super(COMMAND, "Decline the offered new game from the connected user", USAGE);
        this.warShips = warShips;
    }

    @Override
    @Summary({"this.warShips.console.currentCommands", "Stage.CONNECTED.commands"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if (stage != Stage.OFFER_RECEIVED) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 0) {
                    warShips.printUsrMsg(USAGE);
                } else {
                    executeSupervisor();
                }
            } catch (Exception e) {
                warShips.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }
    }

    @Summary({"this.warShips.console.currentCommands", "Stage.CONNECTED.commands"})
    private void executeSupervisor() throws TalkersDeviation {
        BattleBoatsMessage message = BattleBoatsMessage.newBuilder()
                .setType(Type.GAME_DECLINE)
                .build();
        warShips.sendMessage(message.toByteArray());

        warShips.assignStage(Stage.CONNECTED);
    }
}
