package battleboats_1.com.cyberpointllc.stac.battleship;

import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersConnection;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.command.Console;
import battleboats_1.com.cyberpointllc.stac.dispatch.Dispatcher;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.BattleBoatsMessage.Type;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.ErrorMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.Hit;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.HitResultsMessage;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.IWonMessage;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

public class WarShipsDispatcher extends Dispatcher {
    private final WarShips warShips;

    public WarShipsDispatcher(WarShips warShips, Console console) {
        super(console);

        this.warShips = Objects.requireNonNull(warShips, "BattleBoats may not be null");
    }

    @Override
    protected void handleReceivedMessage(byte[] data, TalkersConnection conn) {
        try {
            BattleBoatsMessage message = BattleBoatsMessage.parseFrom(data);
            Stage currentStage = warShips.pullStage();

            if (!isMessageTypeValidForCurrentStage(message.getType(), currentStage)) {
                warShips.printUsrMsg("Ignoring " + message.getType() + " message received in state " + currentStage);
                sendErrorMessage(message, "Message type unexpected in current state");
                return;
            }

            try {
                switch (message.getType()) {
                    case GAME_OFFER:
                        int boardSize = message.getOfferGameMsg().getBoardSize();
                        double squareSize = message.getOfferGameMsg().getSquareSize();
                        int divisors = message.getOfferGameMsg().getDivisors();

                        try {
                            // Make this call first since it may throw an exception
                            warShips.setCompetitionParameters(boardSize, squareSize, divisors);

                            warShips.printUsrMsg("Received game offer from " + conn +
                                    " for a game board of size " + boardSize +
                                    " with squares of length " + squareSize +
                                    " meters with " + divisors + " divisors.");

                            warShips.assignStage(Stage.OFFER_RECEIVED);
                        } catch (IllegalArgumentException e) {
                            warShips.printUsrMsg("Declining game offer request due to invalid parameters: " + e.getMessage());
                            BattleBoatsMessage response = BattleBoatsMessage.newBuilder()
                                    .setType(Type.GAME_DECLINE)
                                    .build();
                            warShips.sendMessage(response.toByteArray());
                        }

                        break;
                    case GAME_ACCEPT:
                        warShips.printUsrMsg(conn + " accepted the game offer.");
                        warShips.startCompetition(true);
                        warShips.assignStage(Stage.LAY_SHIPS);

                        break;
                    case GAME_DECLINE:
                        warShips.printUsrMsg(conn + " declined the game offer.");
                        warShips.assignStage(Stage.CONNECTED);

                        break;
                    case BOATS_PLACED:
                        if (currentStage == Stage.WAIT_FOR_OPPONENT_READY) { // for player 2
                            handleReceivedMessageAssist();
                        } else if (currentStage == Stage.IM_READY) { // for player 1
                            warShips.printUsrMsg("Opponent has placed their boats; begin by declaring your first shot.");
                            warShips.assignStage(Stage.DECLARE_FIRE);
                        }

                        break;
                    case SHOT_MADE:
                        String heightInMeters = message.getShotMsg().getHeight();
                        String speedInMetersPerSecond = message.getShotMsg().getVelocity();
                        String elevationAngle = message.getShotMsg().getVerticalAngle(); // Degrees
                        String boardAngle = message.getShotMsg().getBoardAngle(); // Degrees

                        try {
                            Map<Square, Pin> strikeMap = warShips.fireTaken(heightInMeters, speedInMetersPerSecond, elevationAngle, boardAngle);
                            List<Hit> strikeList = strikeMap.keySet().stream()
                                    .map(sq -> Hit.newBuilder()
                                            .setX(sq.fetchX())
                                            .setY(sq.obtainY())
                                            .setPeg(strikeMap.get(sq).takeName())
                                            .build())
                                    .collect(Collectors.toList());
                            HitResultsMessage msg = HitResultsMessage.newBuilder()
                                    .addAllHit(strikeList)
                                    .build();
                            BattleBoatsMessage bbMsg = BattleBoatsMessage.newBuilder()
                                    .setType(Type.HIT_RESULT)
                                    .setResultMsg(msg)
                                    .build();

                            warShips.sendMessage(bbMsg.toByteArray());
                            warShips.printUsrMsg("Shot has been made with a height of " + heightInMeters +
                                    " m, velocity of " + speedInMetersPerSecond + " m/s, elevation angle of " +
                                    elevationAngle + " degrees, board angle of " + boardAngle + " degrees.");
                            warShips.showStrikeReports(strikeMap);
                            warShips.assignStage(Stage.DECLARE_FIRE);
                        } catch (IllegalArgumentException e) {
                            warShips.printUsrMsg("Received an invalid shot; await re-shot");
                            sendErrorMessage(message, e.getMessage());
                        }

                        break;
                    case HIT_RESULT:
                        List<Hit> strikes = message.getResultMsg().getHitList();
                        if (strikes.isEmpty()) {
                            warShips.printUsrMsg("You did not hit the board!");
                            warShips.assignStage(Stage.WAIT_FOR_FIRE);
                        } else {
                            warShips.setStrikeReports(strikes);

                            if (warShips.iWon()) {
                                IWonMessage win = IWonMessage.newBuilder()
                                        .setWin(true)
                                        .build();
                                BattleBoatsMessage response = BattleBoatsMessage.newBuilder()
                                        .setType(Type.I_WON)
                                        .setWinMsg(win)
                                        .build();
                                warShips.sendMessage(response.toByteArray());
                                warShips.printUsrMsg("You won the game!");
                                warShips.competitionOver();
                            } else {
                                warShips.assignStage(Stage.WAIT_FOR_FIRE);
                            }
                        }

                        break;
                    case I_WON:
                        // This person lost, notify them and end the game; revert back to connected
                        warShips.printUsrMsg("You lost the game!");
                        warShips.competitionOver();

                        break;
                    case ERROR:
                        String reason = message.getErrorMsg().getReason();
                        warShips.revertStage();
                        warShips.printUsrMsg("Last message was rejected: " + reason + ". Please redo.");
                }
            } catch (Exception e) {
                warShips.printUsrMsg("Error handling received message " + message.getType() + ": " + e.getMessage());
                sendErrorMessage(message, "Invalid message: " + message.getType() + ": " + e.getMessage());
            }
        } catch (Exception exc) {
            warShips.printUsrMsg("Error handling message " + exc.getMessage());
        }
    }

    private void handleReceivedMessageAssist() {
        warShips.printUsrMsg("Opponent has placed their boats; please place your boats and their cannon.");
        warShips.assignStage(Stage.LAY_SHIPS);
    }

    private void sendErrorMessage(BattleBoatsMessage rejectedMessage, String reason) {
        ErrorMessage msg = ErrorMessage.newBuilder()
                .setRejectedMessage(rejectedMessage)
                .setReason(reason)
                .build();
        BattleBoatsMessage bbMsg = BattleBoatsMessage.newBuilder()
                .setType(Type.ERROR)
                .setErrorMsg(msg)
                .build();
        try {
            warShips.sendMessage(bbMsg.toByteArray());
        } catch (TalkersDeviation e) {
            warShips.printUsrMsg("Failed to send error message");
        }
    }

    @Override
    protected void handleNewConnection(TalkersConnection conn) throws TalkersDeviation {
        if (!warShips.addConnection(conn)) {
            throw new TalkersDeviation("Connection cannot be established; player likely already involved in a game");
        }
    }

    @Override
    protected void handleClosedConnection(TalkersConnection conn) {
        try {
            warShips.removeConnection(conn);
        } catch (TalkersDeviation e) {
            warShips.printUsrMsg("Error handling closed connection " + e.getMessage());
        }
    }


    private String grabStrikesString(List<Hit> strikes) {
        String strikeStr = "hit squares: ";
        for (int a = 0; a < strikes.size(); a++) {
            Hit strike = strikes.get(a);
            Pin pin = Pin.fromName(strike.getPeg());
            if (pin == Pin.STRIKE) {
                strikeStr += "(" + strike.getX() + ", " + strike.getY() + ") ";
            }
        }
        return strikeStr;
    }

    private static boolean isMessageTypeValidForCurrentStage(Type type, Stage currentStage) {
        switch (type) {
            case GAME_OFFER:
                return (currentStage == Stage.CONNECTED);
            case GAME_ACCEPT:
                return (currentStage == Stage.COMPETITION_OFFERED);
            case GAME_DECLINE:
                return (currentStage == Stage.COMPETITION_OFFERED);
            case BOATS_PLACED:
                return ((currentStage == Stage.IM_READY) || (currentStage == Stage.WAIT_FOR_OPPONENT_READY));
            case SHOT_MADE:
                return (currentStage == Stage.WAIT_FOR_FIRE);
            case HIT_RESULT:
                return (currentStage == Stage.WAIT_FOR_REPORT);
            case I_WON:
                return (currentStage == Stage.DECLARE_FIRE);
        }

        return true;
    }
}
