package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.PrintStream;
import java.util.List;

public class TripleSwapCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(TripleSwapCommand.class);
    private static final String COMMAND = "triple_swap";
    private static final String USAGE = COMMAND + " <seed> ";
    private final PlaitIt plaitIt;

    public TripleSwapCommand(PlaitIt plaitIt) {
        super(COMMAND, "Swap indices on a random permitted triple", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        @Bound("24") int i;
        @Inv("= phase.allowedCommands 12") GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.PLAIT_SELECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof PlaitSelectedPhase) {
            @Inv("= selectedPhase.allowedCommands 12") PlaitSelectedPhase selectedPhase = (PlaitSelectedPhase) phase;

            try {
                if (cmdLine.getArgList().size() != 1) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    long seed = Long.parseLong(cmdLine.getArgList().get(0));
                    logger.info("Triple swap with seed={}", seed);
                    boolean success = selectedPhase.obtainPlait().flipRandomTriple(seed);
                    if (success) {
                        plaitIt.printUsrMsg("Braid is now " + selectedPhase.obtainPlait());
                    } else {
                        plaitIt.printUsrMsg("Unable to perform triple flip on braid " + selectedPhase.obtainPlait());
                    }
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of BriadSelectedState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }
}
