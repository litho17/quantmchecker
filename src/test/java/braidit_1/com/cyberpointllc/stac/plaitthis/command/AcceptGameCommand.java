package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage.Type;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class AcceptGameCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(AcceptGameCommand.class);
    private static final String COMMAND = "accept_game";
    private static final String USAGE = COMMAND;

    private final PlaitIt plaitIt;

    public AcceptGameCommand(PlaitIt plaitIt) {
        super(COMMAND, "Accept offered new game with specified user", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.OFFER_RECEIVED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else {
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 0) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    logger.info("Accepted game offer");
                    plaitIt.startGame(false);
                    plaitIt.setStep(new GamePhase(GamePhase.Phase.AWAIT_PLAIT_LENGTHS)); // other player goes first
                    BraidItMessage message = BraidItMessage.newBuilder()
                            .setType(Type.GAME_ACCEPT)
                            .build();
                    plaitIt.transmitMessage(message.toByteArray());
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
                e.printStackTrace();
            }
        }
    }
}
