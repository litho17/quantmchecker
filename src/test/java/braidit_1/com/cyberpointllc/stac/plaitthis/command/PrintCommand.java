package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plait.Plait;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class PrintCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(PrintCommand.class);
    private static final String COMMAND = "print";
    private static final String USAGE = COMMAND;
    private final PlaitIt plaitIt;

    public PrintCommand(PlaitIt plaitIt) {
        super(COMMAND, "Print the braids", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!isCorrectPhase(phase)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else {
            try {
                if (cmdLine.getArgList().size() != 0) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    ChoicesPhase choicesPhase = plaitIt.obtainCurrentGame().getChoicesPhase();

                    if (choicesPhase != null) {
                        boolean introPrinted = false;

                        for (int i = 1; i <= 5; i++) {
                            Plait plait = choicesPhase.fetchPlait(i);

                            if (plait != null) {
                                if (!introPrinted) {
                                    introPrinted = true;
                                    plaitIt.printUsrMsg("Braids:");
                                }

                                plaitIt.printUsrMsg(String.format("%d: %s", i, plait.toString()));
                            }
                        }
                    }

                    if (phase instanceof PlaitSelectedPhase) {
                        PlaitSelectedPhase selectedPhase = (PlaitSelectedPhase) phase;
                        Plait plait = selectedPhase.obtainPlait();

                        if (plait != null) {
                            executeHelp(plait);
                        }
                    }
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }
    }

    private void executeHelp(Plait plait) {
        if (plaitIt.obtainCurrentGame().doIGoFirst()) {
            plaitIt.printUsrMsg("Received modified braid: " + plait);
        } else {
            plaitIt.printUsrMsg("Selected braid: " + plait);
        }
    }

    private static boolean isCorrectPhase(GamePhase phase) {
        return
                phase.matches(GamePhase.Phase.RECEIVED_MODIFIED_PLAIT) ||
                phase.matches(GamePhase.Phase.RECEIVED_PLAIT_LENGTHS) ||
                phase.matches(GamePhase.Phase.PLAIT_SELECTED);
    }
}
