package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import org.apache.commons.cli.CommandLine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.util.List;

public class DisconnectCommand extends PlaitItCommand {
    private static final Logger logger = LoggerFactory.getLogger(DisconnectCommand.class);
    private static final String COMMAND = "disconnect";
    private static final String USAGE = COMMAND;

    private final PlaitIt plaitIt;

    public DisconnectCommand(PlaitIt plaitIt) {
        super(COMMAND, "disconnect from current connection", USAGE);
        this.plaitIt = plaitIt;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        try {
            if (cmdLine.getArgList().size() != 0) {
                out.println(USAGE);
            } else {
                logger.info("Disconnecting...");
                if (plaitIt.hasConnection()) {
                    plaitIt.disconnect();
                } else {
                    plaitIt.printUsrMsg("Cannot disconnect -- no connection exists");
                }
            }
        } catch (Exception e) {
            plaitIt.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }
}
