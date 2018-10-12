package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.LengthsPhase;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class AssignLengthCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(AssignLengthCommand.class);
    private static final String COMMAND = "set_length";
    private static final String USAGE = COMMAND + "<braid_num> <length>";
    private final PlaitIt plaitIt;

    public AssignLengthCommand(PlaitIt plaitIt) {
        super(COMMAND, "Sets the length of one of the 5 initial braids (1, 2, 3, 4, 5) to be presented to the other user", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        @Bound("24") int i;
        @Inv("= phase.allowedCommands 12") GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);

        if (!phase.matches(GamePhase.Phase.SELECTING_LENGTHS) && !phase.matches(GamePhase.Phase.LENGTHS_SELECTED) ){
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof LengthsPhase){
            @Inv("= lengthsPhase.allowedCommands 12") LengthsPhase lengthsPhase = (LengthsPhase) phase;

            try {
                if (cmdLine.getArgList().size() != 2) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    int plaitNum = Integer.parseInt(cmdLine.getArgList().get(0));
                    int length = Integer.parseInt(cmdLine.getArgList().get(1));

                    if (plaitNum <= 0 || plaitNum > 5) {
                        plaitIt.printUsrMsg("braid_num must be 1, 2, 3, 4, or 5");
                        return;
                    }

                    logger.info("Setting length on braid number={} length={}", plaitNum, length);
                    plaitIt.printUsrMsg("Braid " + plaitNum + " set to length " + length);
                    boolean fiveChosen = lengthsPhase.placeLength(plaitNum, length);
                    if (fiveChosen){
                        System.out.println("Set state to " + phase);
                        plaitIt.setStep(phase); // state has already been updated internally, just need to let BraidIt know
                    }
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of LengthsState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }
}
