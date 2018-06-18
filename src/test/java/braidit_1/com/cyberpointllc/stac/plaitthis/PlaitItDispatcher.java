package braidit_1.com.cyberpointllc.stac.plaitthis;

import braidit_1.com.cyberpointllc.stac.plait.Plait;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.LengthsPhase;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsConnection;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.console.Display;
import braidit_1.com.cyberpointllc.stac.dispatch.Dispatcher;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedStepBuilder;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage.Type;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.ErrorMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.LengthsMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.ModifiedBraidMessage;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.Objects;

/**
 * Handles the provided messages and console commands in the order that they are received
 */
public class PlaitItDispatcher extends Dispatcher {
    private static final Logger logger = LoggerFactory.getLogger(PlaitItDispatcher.class);

    private final PlaitIt plaitIt;

    public PlaitItDispatcher(PlaitIt plaitIt, Display display) {
        super(display);
        this.plaitIt = Objects.requireNonNull(plaitIt, "BraidIt may not be null");
    }

    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void handleReceivedMessage(byte[] data, CommunicationsConnection conn) {
        try {
            // parse the message
            BraidItMessage msg = BraidItMessage.parseFrom(data);

            try {
                // determine what type of message we have and handle it accordingly
                switch (msg.getType()) {
                    case GAME_OFFER:
                        if (plaitIt.getStep().matches(GamePhase.Phase.CONNECTED)) {
                            int numFibers = msg.getGameOfferMsg().getNumStrands();
                            if (numFibers <= 0) {
                                throw new Exception("Number of strands must be positive: " + numFibers);
                            }
                            plaitIt.printUsrMsg("Received game offer with " + numFibers + " strands from " + conn);
                            plaitIt.fixNumFibers(numFibers);
                            plaitIt.setStep(new GamePhase(GamePhase.Phase.OFFER_RECEIVED));
                            record(msg.getType(), GamePhase.Phase.CONNECTED, GamePhase.Phase.OFFER_RECEIVED);
                        } else {
                            handleReceivedMessageManager(msg);
                        }

                        break;
                    case GAME_ACCEPT:
                        if (plaitIt.getStep().matches(GamePhase.Phase.GAME_OFFERED)) {
                            plaitIt.printUsrMsg(conn + " accepted game offer");
                            plaitIt.startGame(true);
                            plaitIt.setStep(new LengthsPhase(GamePhase.Phase.SELECTING_LENGTHS)); // I offered, I get to go first
                            record(msg.getType(), GamePhase.Phase.GAME_OFFERED, GamePhase.Phase.SELECTING_LENGTHS);
                        } else {
                            new PlaitItDispatcherGuide(msg).invoke();
                        }

                        break;
                    case GAME_DECLINE:
                        if (plaitIt.getStep().matches(GamePhase.Phase.GAME_OFFERED)) {
                            new PlaitItDispatcherFunction(conn, msg).invoke();
                        } else {
                            new PlaitItDispatcherHelper(msg).invoke();
                        }

                        break;
                    case LENGTHS:
                        if (plaitIt.getStep().matches(GamePhase.Phase.AWAIT_PLAIT_LENGTHS)) {
                            LengthsMessage lengthsMsg = msg.getLengthsMsg();
                            int length1 = lengthsMsg.getLength1();
                            int length2 = lengthsMsg.getLength2();
                            int length3 = lengthsMsg.getLength3();
                            int length4 = lengthsMsg.getLength4();
                            int length5 = lengthsMsg.getLength5();
                            validateLength(length1);
                            validateLength(length2);
                            validateLength(length3);
                            validateLength(length4);
                            validateLength(length5);

                            ChoicesPhase choicesPhase = new ChoicesPhase(GamePhase.Phase.RECEIVED_PLAIT_LENGTHS);
                            int fibers = plaitIt.obtainCurrentGame().takeNumFibers();
                            Plait braid1 = Plait.pullRandomPlait(fibers, length1);
                            Plait braid2 = Plait.pullRandomPlait(fibers, length2);
                            Plait braid3 = Plait.pullRandomPlait(fibers, length3);
                            Plait braid4 = Plait.pullRandomPlait(fibers, length4);
                            Plait braid5 = Plait.pullRandomPlait(fibers, length5);
                            choicesPhase.putPlait(1, braid1);
                            choicesPhase.putPlait(2, braid2);
                            choicesPhase.putPlait(3, braid3);
                            choicesPhase.putPlait(4, braid4);
                            choicesPhase.putPlait(5, braid5);

                            plaitIt.printUsrMsg("Got choices:");
                            plaitIt.printUsrMsg("1: " + braid1);
                            plaitIt.printUsrMsg("2: " + braid2);
                            plaitIt.printUsrMsg("3: " + braid3);
                            plaitIt.printUsrMsg("4: " + braid4);
                            plaitIt.printUsrMsg("5: " + braid5);
                            plaitIt.setStep(choicesPhase);
                            record(msg.getType(), GamePhase.Phase.AWAIT_PLAIT_LENGTHS, GamePhase.Phase.RECEIVED_PLAIT_LENGTHS);
                        } else {
                            plaitIt.printUsrMsg("Ignoring CHOICES message received in state " + plaitIt.getStep());
                            record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
                        }

                        break;
                    case MODIFIED_BRAID:
                        if (plaitIt.getStep().matches(GamePhase.Phase.AWAIT_MODIFIED_PLAIT)) {
                            ModifiedBraidMessage plaitMsg = msg.getBraidMsg();
                            String plait = plaitMsg.getBraid();
                            String braid1 = plaitMsg.getBraid1();
                            String braid2 = plaitMsg.getBraid2();
                            String braid3 = plaitMsg.getBraid3();
                            String braid4 = plaitMsg.getBraid4();
                            String braid5 = plaitMsg.getBraid5();
                            int numFibers = plaitIt.obtainCurrentGame().takeNumFibers();
                            // since we are now only finding out the choices now, we briefly pass through a choices state to set the choices
                            ChoicesPhase choicesPhase = new ChoicesPhase(GamePhase.Phase.LENGTHS_SELECTED);
                            choicesPhase.putPlait(1, new Plait(braid1, numFibers));
                            choicesPhase.putPlait(2, new Plait(braid2, numFibers));
                            choicesPhase.putPlait(3, new Plait(braid3, numFibers));
                            choicesPhase.putPlait(4, new Plait(braid4, numFibers));
                            choicesPhase.putPlait(5, new Plait(braid5, numFibers));
                            plaitIt.setStep(choicesPhase);
                            // now go to the actual BraidSelectedState
                            PlaitSelectedPhase phase = new PlaitSelectedStepBuilder().fixAdvance(GamePhase.Phase.RECEIVED_MODIFIED_PLAIT).composePlaitSelectedStep();
                            phase.insertPlait(new Plait(plait, numFibers));
                            plaitIt.printUsrMsg("Received modified braid: " + plait);
                            plaitIt.setStep(phase);
                            record(msg.getType(), GamePhase.Phase.AWAIT_MODIFIED_PLAIT, GamePhase.Phase.RECEIVED_MODIFIED_PLAIT);
                        } else {
                            new PlaitItDispatcherAdviser(msg).invoke();
                        }
                        break;
                    case ROUND_OUTCOME:
                        if (plaitIt.getStep().matches(GamePhase.Phase.AWAIT_OUTCOME)) {
                            boolean iLost = msg.getOutcomeMsg().getFirstUserWon();
                            plaitIt.printUsrMsg("Notified that I " + (iLost ? "lost" : "won") + " the current round");
                            boolean gameOver = plaitIt.finishedRound(!iLost);
                            plaitIt.printUsrMsg(plaitIt.obtainCurrentGame().pullStats());
                            if (gameOver) {
                                plaitIt.gameOver();
                            } else {
                                plaitIt.printUsrMsg("Next round begins...; start making braids");
                                plaitIt.setStep(plaitIt.obtainCurrentGame().pullPhase());
                            }
                            record(msg.getType(), GamePhase.Phase.AWAIT_OUTCOME, plaitIt.getStep().getStep());
                        } else {
                            plaitIt.printUsrMsg("Ignoring ROUND_OUTCOME message received in state " + plaitIt.getStep());
                            record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
                        }

                        break;
                    case ERROR_MESSAGE:
                        String reason = msg.getErrorMsg().getReason();
                        plaitIt.printUsrMsg("Error processing message: " + reason);
                        break;
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Error handling message: " + msg.getType() + ": " + e.getMessage());
                ErrorMessage errorMessage = ErrorMessage.newBuilder()
                        .setReason("Invalid message: " + msg.getType() + ": " + e.getMessage())
                        .build();
                BraidItMessage outmsg = BraidItMessage.newBuilder()
                        .setType(Type.ERROR_MESSAGE)
                        .setErrorMsg(errorMessage)
                        .build();
                plaitIt.transmitMessage(outmsg.toByteArray());
            }
        } catch (Exception ex) {
            plaitIt.printUsrMsg("Error processing message " + ex.getMessage());
        }
    }

    private void handleReceivedMessageManager(BraidItMessage msg) {
        plaitIt.printUsrMsg("Ignoring game offer received in state" + plaitIt.getStep());
        record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
    }

    @Override
    public void handleNewConnection(CommunicationsConnection conn) throws CommunicationsException {
        logger.debug("New Connection request from {}" + conn);
        if (!plaitIt.addConnection(conn)) {
            throw new CommunicationsException("Connection cannot be established; player likely already involved in a game");
        }
    }

    @Override
    public void handleClosedConnection(CommunicationsConnection conn) throws CommunicationsException {
        try {
            logger.debug("Connection closed from {}" + conn);
            plaitIt.removeConnection(conn);
        } catch (CommunicationsException e) {
            plaitIt.printUsrMsg("Error handling closed connection " + e.getMessage());
        }
    }

    private void validateLength(int length){
        if (length <= 0 || length > Plait.MAX_LENGTH) {
            logger.debug("Received invalid braid length");
            GamePhase.fixErrorStep("INVALID_LENGTH");
            throw new IllegalArgumentException("Braid length must be between 1 and " + Plait.MAX_LENGTH);
        }
    }

    private void record(Type type, GamePhase.Phase oldPhase, GamePhase.Phase newPhase) {
        logger.info("Received message of type " + type + ". State: " + oldPhase + "->" + newPhase);
    }

    private class PlaitItDispatcherGuide {
        private BraidItMessage msg;

        public PlaitItDispatcherGuide(BraidItMessage msg) {
            this.msg = msg;
        }

        public void invoke() {
            plaitIt.printUsrMsg("Ignoring GAME_ACCEPT message received in state " + plaitIt.getStep());
            record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
        }
    }

    private class PlaitItDispatcherFunction {
        private CommunicationsConnection conn;
        private BraidItMessage msg;

        public PlaitItDispatcherFunction(CommunicationsConnection conn, BraidItMessage msg) {
            this.conn = conn;
            this.msg = msg;
        }

        public void invoke() {
            plaitIt.printUsrMsg(conn + " declined game offer");
            plaitIt.setStep(new GamePhase(GamePhase.Phase.CONNECTED));
            record(msg.getType(), GamePhase.Phase.GAME_OFFERED, GamePhase.Phase.CONNECTED);
        }
    }

    private class PlaitItDispatcherHelper {
        private BraidItMessage msg;

        public PlaitItDispatcherHelper(BraidItMessage msg) {
            this.msg = msg;
        }

        public void invoke() {
            plaitIt.printUsrMsg("Ignoring GAME_DECLINE message received in state " + plaitIt.getStep());
            record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
        }
    }

    private class PlaitItDispatcherAdviser {
        private BraidItMessage msg;

        public PlaitItDispatcherAdviser(BraidItMessage msg) {
            this.msg = msg;
        }

        public void invoke() {
            plaitIt.printUsrMsg("Ignoring MODIFIED_BRAID message received in state " + plaitIt.getStep());
            record(msg.getType(), plaitIt.getStep().getStep(), plaitIt.getStep().getStep());
        }
    }
}
