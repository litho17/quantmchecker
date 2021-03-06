package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plait.Plait;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage.Type;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.OutcomeMessage;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class MakeGuessCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(MakeGuessCommand.class);
    private static final String COMMAND = "make_guess";
    private static final String USAGE = COMMAND + " <num> ";
    private final PlaitIt plaitIt;

    public MakeGuessCommand(PlaitIt plaitIt) {
        super(COMMAND, "Guess which of the five original braids the modified braid represents", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.previousRounds", "2", "this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        @Bound("36") int i;
        @Inv("= phase.allowedCommands 12") GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.RECEIVED_MODIFIED_PLAIT)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof PlaitSelectedPhase) {
            try {
                if (cmdLine.getArgList().size() != 1) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    int selection = Integer.parseInt(cmdLine.getArgList().get(0));
                    if (selection <= 0 || selection > 5) {
                        plaitIt.printUsrMsg(COMMAND + " must be used with a selection between 1 and 5");
                        return;
                    }
                    // check if correct
                    @Inv("= selectedPhase.allowedCommands 12") PlaitSelectedPhase selectedPhase = (PlaitSelectedPhase) phase;
                    Plait received = selectedPhase.obtainPlait();
                    @Inv("= choicesPhase.allowedCommands 12") ChoicesPhase choicesPhase = plaitIt.obtainCurrentGame().getChoicesPhase();
                    Plait original = choicesPhase.fetchPlait(selection);
                    boolean iWon = received.isEquivalent(original);
                    logger.info("Guessed braid number={} correct={}", selection, iWon);
                    if (iWon) {
                        plaitIt.printUsrMsg("I won this round!");
                    } else {
                        plaitIt.printUsrMsg("I lost this round.");
                    }

                    // notify other player
                    OutcomeMessage outcomeMsg = OutcomeMessage.newBuilder()
                            .setFirstUserWon(iWon)
                            .build();
                    BraidItMessage msg = BraidItMessage.newBuilder()
                            .setType(Type.ROUND_OUTCOME)
                            .setOutcomeMsg(outcomeMsg)
                            .build();
                    plaitIt.printUsrMsg("Sending round outcome to other player");
                    plaitIt.transmitMessage(msg.toByteArray());
                    // mark round as complete
                    boolean gameOver = plaitIt.finishedRound(iWon);
                    plaitIt.printUsrMsg(plaitIt.obtainCurrentGame().pullStats());
                    if (gameOver) {
                        plaitIt.gameOver();
                    } else {
                        executeManager();
                    }
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
                e.printStackTrace();
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of BriadSelectedState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }

    private void executeManager() {
        plaitIt.printUsrMsg("Next round begins...; other player will send braid lengths to you soon");
        plaitIt.setStep(plaitIt.obtainCurrentGame().pullPhase()); // now other player's turn to go first
    }
}
