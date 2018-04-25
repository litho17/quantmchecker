package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage.Type;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class DeclineGameCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(DeclineGameCommand.class);
    private static final String COMMAND = "decline_game";
    private static final String USAGE = COMMAND;

    private final PlaitIt plaitIt;

    public DeclineGameCommand(PlaitIt plaitIt) {
        super(COMMAND, "Decline offered new game", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.OFFER_RECEIVED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else {
            executeHelper(cmdLine);
        }
    }

    private void executeHelper(CommandLine cmdLine) {
        try {
            List<String> argList = cmdLine.getArgList();
            if (argList.size() != 0) {
                plaitIt.printUsrMsg(USAGE);
            } else {
                new DeclineGameCommandTarget().invoke();
            }
        } catch (Exception e) {
            plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private class DeclineGameCommandTarget {
        public void invoke() throws CommunicationsException {
            logger.info("Declining game offer");
            plaitIt.setStep(new GamePhase(GamePhase.Phase.CONNECTED));
            BraidItMessage message = BraidItMessage.newBuilder()
                    .setType(Type.GAME_DECLINE)
                    .build();
            plaitIt.transmitMessage(message.toByteArray());
        }
    }
}
