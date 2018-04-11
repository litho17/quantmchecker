package battleboats_1.com.cyberpointllc.stac.command;

import java.io.PrintStream;

/**
 * Handles lines that don't seem to be commands
 */
public interface LineManager {

    void handleLine(String line, PrintStream out);

}
