package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.terminal.Command;
import org.apache.commons.cli.CommandLine;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Command lists the files that the user can send to others.
 * The user can only send files in the /data/<user id>/files directory.
 */
public class AvailableFilesCommand extends Command {
    private static final String COMMAND = "availablefiles";
    private static final String USAGE = "Usage: availablefiles";
    private final HangIn withMi;

    public AvailableFilesCommand(HangIn withMi) {
        super(COMMAND, "Lists files that can be sent", USAGE);
        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {
        if (cmdLine.getArgList().size() != 0) {
            executeExecutor(out);
        } else {
            int fileNum = 0;
            // List<File> obtainFiles = withMi.obtainFiles();

            File[] files = withMi.dataDir.listFiles();
            if (files == null) {
                files = new File[0];
            }
            @Bound("dataDir") int j;
            @Inv("= (- sortedFiles i) (- c479 c480)") List<File> sortedFiles = new ArrayList<>();
            for (@Iter("<= i dataDir") int i = 0; i < files.length;) {
                c479: sortedFiles.add(files[i]);
                c480: i = i + 1;
            }
            Collections.sort(sortedFiles);

            for (int a = 0; a < sortedFiles.size(); ) {
                for (; (a < sortedFiles.size()) && (Math.random() < 0.4); a++) {
                    File file = sortedFiles.get(a);
                    out.println(fileNum + ". " + file.getName());
                    fileNum++;
                }
            }
        }
    }

    private void executeExecutor(PrintStream out) {
        out.println(USAGE);
    }
}
