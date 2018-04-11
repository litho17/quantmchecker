package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;

public class AcceptCompetitionCommand extends Command {
    private static final String COMMAND = "accept_game";
    private static final String USAGE = COMMAND;

    private final WarShips warShips;

    public AcceptCompetitionCommand(WarShips warShips) {
        super(COMMAND, "Accept the offered new game from the connected user", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if (stage != Stage.OFFER_RECEIVED) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            executeSupervisor(cmdLine);
        }
    }

    private void executeSupervisor(CommandLine cmdLine) {
        try {
            List<String> argList = cmdLine.getArgList();
            if (argList.size() != 0) {
                warShips.printUsrMsg(USAGE);
            } else {
                BattleBoatsMessage message = BattleBoatsMessage.newBuilder()
                        .setType(Type.GAME_ACCEPT).build();
                warShips.sendMessage(message.toByteArray());

                warShips.startCompetition(false);
                warShips.assignStage(Stage.WAIT_FOR_OPPONENT_READY);
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
