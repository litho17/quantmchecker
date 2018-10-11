package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.command.Command;
import org.apache.commons.cli.CommandLine;

import java.io.PrintStream;
import java.io.StringWriter;
import java.util.List;

public class PrintBoardCommand extends Command {
    private static final String COMMAND = "print";
    private static final String USAGE = COMMAND + " radar | ocean";

    private final WarShips warShips;

    public PrintBoardCommand(WarShips warShips) {
        super(COMMAND, "Print out the Ocean or Radar board", USAGE);
        this.warShips = warShips;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        Stage stage = warShips.pullStage();
        if (isStageInvalid(stage)) {
            warShips.printUsrMsg("Command " + COMMAND + " is illegal in state " + stage);
        } else {
            executeSupervisor(out, cmdLine);
        }
    }

    private void executeSupervisor(PrintStream out, CommandLine cmdLine) {
        try {
            List<String> argList = cmdLine.getArgList();
            if (argList.size() != 1) {
                out.println(USAGE);
            } else {
                String name = argList.get(0).trim();
                StringWriter stringWriter = new StringWriter();
                if ("ocean".equalsIgnoreCase(name)) {
                    warShips.printOcean(stringWriter);
                    warShips.printUsrMsg(stringWriter.toString());
                } else if ("radar".equalsIgnoreCase(name)) {
                    warShips.printRadar(stringWriter);
                    warShips.printUsrMsg(stringWriter.toString());
                } else {
                    warShips.printUsrMsg("Not a valid command argument: " + name);
                }
            }
        } catch (Exception e) {
            warShips.printUsrMsg("Problem processing command: " + e.getMessage());
        }
    }

    private static boolean isStageInvalid(Stage stage) {
        return ((stage == Stage.IDLE) ||
                (stage == Stage.CONNECTED) ||
                (stage == Stage.COMPETITION_OFFERED) ||
                (stage == Stage.OFFER_RECEIVED));
    }
}
