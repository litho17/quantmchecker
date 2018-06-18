package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.PlaitSelectedPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.ModifiedBraidMessage;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class TransmitModifiedPlaitCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(TransmitModifiedPlaitCommand.class);
    private static final String COMMAND = "send_modified";
    private static final String USAGE = COMMAND;
    private final PlaitIt plaitIt;

    public TransmitModifiedPlaitCommand(PlaitIt plaitIt) {
        super(COMMAND, "Send the modified braid to the other player", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);
        if (!phase.matches(GamePhase.Phase.PLAIT_SELECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof PlaitSelectedPhase) {
            new TransmitModifiedPlaitCommandCoordinator(cmdLine, (PlaitSelectedPhase) phase).invoke();
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of BriadSelectedState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }

    private class TransmitModifiedPlaitCommandCoordinator {
        private CommandLine cmdLine;
        private PlaitSelectedPhase phase;

        public TransmitModifiedPlaitCommandCoordinator(CommandLine cmdLine, PlaitSelectedPhase step) {
            this.cmdLine = cmdLine;
            this.phase = step;
        }

        public void invoke() {
            PlaitSelectedPhase selectedPhase = phase;

            try {
                List<String> argList = cmdLine.getArgList();
                if (argList.size() != 0) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    invokeExecutor(selectedPhase);
                }
            } catch (Exception e) {
                plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
            }
        }

        private void invokeExecutor(PlaitSelectedPhase selectedPhase) throws CommunicationsException {
            logger.info("Sending modified braid");
            ChoicesPhase choices = plaitIt.obtainCurrentGame().getChoicesPhase();
            choices.fixFinished(true);
            ModifiedBraidMessage plaitMsg = ModifiedBraidMessage.newBuilder()
                    .setBraid(selectedPhase.getPlaitString())
                    .setBraid1(choices.fetchPlait(1).toString())
                    .setBraid2(choices.fetchPlait(2).toString())
                    .setBraid3(choices.fetchPlait(3).toString())
                    .setBraid4(choices.fetchPlait(4).toString())
                    .setBraid5(choices.fetchPlait(5).toString())
                    .build();

            BraidItMessage msg = BraidItMessage.newBuilder()
                    .setType(BraidItMessage.Type.MODIFIED_BRAID)
                    .setBraidMsg(plaitMsg)
                    .build();
            plaitIt.transmitMessage(msg.toByteArray());
            plaitIt.setStep(new GamePhase(GamePhase.Phase.AWAIT_OUTCOME));
        }
    }
}
