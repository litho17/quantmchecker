package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class GrowToThreeCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(GrowToThreeCommand.class);
    private static final String COMMAND = "expand3";
    private static final String USAGE = COMMAND + " <index> ";
    private final PlaitIt plaitIt;

    public GrowToThreeCommand(PlaitIt plaitIt) {
        super(COMMAND, "Expand the crossing at index to three crossings, if permitted", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.PLAIT_SELECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof PlaitSelectedPhase) {
            PlaitSelectedPhase selectedPhase = (PlaitSelectedPhase) phase;
            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 1) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    executeHelp(selectedPhase, argList);
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of BriadSelectedState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }

    private void executeHelp(PlaitSelectedPhase selectedPhase, List<String> argList) {
        int index = Integer.parseInt(argList.get(0));
        logger.info("Expanding 1-3 index={}", index);
        boolean success = selectedPhase.obtainPlait().growOneToThree(index);
        if (success) {
            plaitIt.printUsrMsg("Braid is now " + selectedPhase.obtainPlait());
        } else {
            plaitIt.printUsrMsg("Unable to perform expand3 on braid " + selectedPhase.obtainPlait() + " at index " + index);
        }
    }
}
