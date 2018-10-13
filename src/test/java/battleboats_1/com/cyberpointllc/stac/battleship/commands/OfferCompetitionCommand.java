package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.OfferGameMessage;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.util.List;
import java.util.Objects;

public class OfferCompetitionCommand extends Command {
    private static final String COMMAND = "offer_game";
    private static final String USAGE = COMMAND + " <board size 10 to 20 squares> <square size 1.0 to 10.0 meters> <divisors 1 to 15>";

    private final WarShips warShips;

    public OfferCompetitionCommand(WarShips warShips) {
        super(COMMAND, "Offer new game with the specified game parameters", USAGE);
        this.warShips = Objects.requireNonNull(warShips, "BattleBoats may not be null");
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {

        if (warShips.pullStage() != Stage.CONNECTED) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal from " + warShips.pullStage() + ".  Try to connect first.");
        } else {
            executeAid(cmdLine);
        }
    }

    private void executeAid(CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 3) {
                warShips.printUsrMsg(USAGE);
            } else {
                int boardSize = Integer.parseInt(cmdLine.getArgList().get(0));
                double squareSize = Double.parseDouble(cmdLine.getArgList().get(1));
                int divisors = Integer.parseInt(cmdLine.getArgList().get(2));

                // Execute this before sending message as it may
                // fail if any arguments are illegal.
                warShips.setCompetitionParameters(boardSize, squareSize, divisors);

                OfferGameMessage offer = OfferGameMessage.newBuilder()
                        .setBoardSize(boardSize)
                        .setSquareSize(squareSize)
                        .setDivisors(divisors)
                        .build();
                BattleBoatsMessage message = BattleBoatsMessage.newBuilder()
                        .setType(Type.GAME_OFFER)
                        .setOfferGameMsg(offer)
                        .build();
                warShips.sendMessage(message.toByteArray());

                warShips.assignStage(Stage.COMPETITION_OFFERED);
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }
}
