package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.LengthsPhase;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.BraidItMessage;
import braidit_1.com.cyberpointllc.stac.proto.Braidit.LengthsMessage;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.PrintStream;
import java.util.List;

public class TransmitLengthsCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(TransmitLengthsCommand.class);
    private static final String COMMAND = "send_lengths";
    private static final String USAGE = COMMAND;
    private final PlaitIt plaitIt;

    public TransmitLengthsCommand(PlaitIt plaitIt) {
        super(COMMAND, "Send the lengths for the five initial braids to the other player", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    @Summary({"this.plaitIt.currentGame.currentRound.phases", "1"})
    public void execute(PrintStream out, CommandLine cmdLine) {
        GamePhase phase = plaitIt.getStep();
        logger.debug("Command {} in state {}", COMMAND, phase);

        if (!phase.matches(GamePhase.Phase.LENGTHS_SELECTED)) {
            plaitIt.printUsrMsg("Command " + COMMAND + " is illegal in state " + plaitIt.getStep());
        } else if (phase instanceof LengthsPhase) {
            LengthsPhase lengthsPhase = (LengthsPhase) phase;
            try {
                if (cmdLine.getArgList().size() != 0) {
                    plaitIt.printUsrMsg(USAGE);
                } else {
                    logger.info("Sending braids");
                    LengthsMessage lengths = LengthsMessage.newBuilder()
                            .setLength1(lengthsPhase.grabLength(1))
                            .setLength2(lengthsPhase.grabLength(2))
                            .setLength3(lengthsPhase.grabLength(3))
                            .setLength4(lengthsPhase.grabLength(4))
                            .setLength5(lengthsPhase.grabLength(5))
                            .build();
                    BraidItMessage msg = BraidItMessage.newBuilder()
                            .setType(BraidItMessage.Type.LENGTHS)
                            .setLengthsMsg(lengths)
                            .build();
                    plaitIt.transmitMessage(msg.toByteArray());
                    plaitIt.setStep(new GamePhase(GamePhase.Phase.AWAIT_MODIFIED_PLAIT));
                }
            } catch (Exception e) {
                out.println("Problem processing command: " + e.getMessage());
                e.printStackTrace(out);
            }
        } else {
            plaitIt.printUsrMsg("Problem processing command: Internal State is invalid.  It should be an instance of LengthsState but is " + phase + " (" + phase.getClass().getName() + ")");
        }
    }
}
