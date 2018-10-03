package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plait.Plait;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedStepBuilder;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class SelectPlaitCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(SelectPlaitCommand.class);
    private static final String COMMAND = "select_braid";
    private static final String USAGE = COMMAND + "<braid_num>";
    private final PlaitIt plaitIt;

    public SelectPlaitCommand(PlaitIt plaitIt) {
        super(COMMAND, "Selects one of the 5 braids to be modified and presented to the other user", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.RECEIVED_PLAIT_LENGTHS) && !phase.matches(GamePhase.Phase.PLAIT_SELECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof ChoicesPhase) {
            ChoicesPhase choicesPhase = (ChoicesPhase) phase;

            try {
                if (cmdLine.getArgList().size() != 1) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    int plaitNum = Integer.parseInt(cmdLine.getArgList().get(0));

                    if (plaitNum <= 0 || plaitNum > 5) {
                        plaitIt.printUsrMsg("braid_num must be 1, 2, 3, 4, or 5");
                        return;
                    }
                    logger.info("Selecting braid number={}", plaitNum);
                    // make copy of so modification doesn't change original
                    Plait plait = new Plait(choicesPhase.fetchPlait(plaitNum).toString(), choicesPhase.fetchPlait(plaitNum).takeNumFibers());
                    PlaitSelectedPhase newPhase = new PlaitSelectedStepBuilder().fixAdvance(GamePhase.Phase.PLAIT_SELECTED).composePlaitSelectedStep();
                    if (choicesPhase.grabErrorStep() != null) {
                        newPhase.insertPlait(plait, plaitNum);
                    } else {
                        newPhase.insertPlait(plait);
                    }
                    plaitIt.setStep(newPhase);
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of ChoicesState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }
}
