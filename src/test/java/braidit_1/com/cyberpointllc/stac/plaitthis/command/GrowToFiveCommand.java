package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.PrintStream;
import java.util.List;

public class GrowToFiveCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(GrowToFiveCommand.class);
    private static final String COMMAND = "expand5";
    private static final String USAGE = COMMAND + " <index> ";
    private final PlaitIt plaitIt;

    public GrowToFiveCommand(PlaitIt plaitIt) {
        super(COMMAND, "Expand the crossing at index to five crossings, if permitted", USAGE);
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
                    int index = Integer.parseInt(cmdLine.getArgList().get(0));
                    logger.info("Expanding 1-5 index={}", index);
                    boolean success = selectedPhase.obtainPlait().growOneToFive(index);
                    if (success) {
                        plaitIt.printUsrMsg("Braid is now " + selectedPhase.obtainPlait());
                    } else {
                        plaitIt.printUsrMsg("Unable to perform expand5 on braid " + selectedPhase.obtainPlait() + " at index " + index);
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
