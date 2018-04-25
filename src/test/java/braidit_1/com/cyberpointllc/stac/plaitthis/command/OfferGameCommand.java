package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage.Type;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.GameOfferMessage;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class OfferGameCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(OfferGameCommand.class);
    private static final String COMMAND = "offer_game";
    private static final String USAGE = COMMAND + " <num strands>";
    private final PlaitIt plaitIt;

    public OfferGameCommand(PlaitIt plaitIt) {
        super(COMMAND, "Request a new game with the specified number of strands", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.CONNECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else {
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 1) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    int numFibers = Integer.parseInt(argList.get(0));
                    if (numFibers <= 0) {
                        throw new Exception("Number of strands must be positive: " + numFibers);
                    }
                    logger.info("Offering game with number of strands={}", numFibers);
                    GameOfferMessage offer = GameOfferMessage.newBuilder()
                            .setNumStrands(numFibers)
                            .build();
                    BraidItMessage message = BraidItMessage.newBuilder()
                            .setType(Type.GAME_OFFER)
                            .setGameOfferMsg(offer)
                            .build();
                    plaitIt.transmitMessage(message.toByteArray());
                    plaitIt.fixNumFibers(numFibers);
                    plaitIt.setStep(new GamePhase(GamePhase.Phase.GAME_OFFERED));
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }
    }
}
