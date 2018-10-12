package withmi_1.edu.networkcusp.chatbox;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.terminal.Command;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.StringsCompleter;
import org.apache.commons.cli.CommandLine;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Command that lets the user send a file to the person they are chatting with.
 * They can only sent files in the data/<user id>/files directory.
 * The files will be sent to the data/<other user id>/incoming directory.
 */
public class DeliverFileZlibCommand extends Command {
    private static final String COMMAND = "sendfilezlib";
    private static final String USAGE = "Usage: sendfilezlib <file number>";
    private static final String SENDING = "I sent a file.";

    private final HangIn withMi;

    public DeliverFileZlibCommand(HangIn withMi) {
        super(COMMAND,
                "Sends the specified file with ZLIB compression",
                USAGE,
                new AggregateCompleter(
                        new ArgumentCompleter(
                                new StringsCompleter(COMMAND),
                                new DeliverFileCompleter(withMi)
                        )
                )
        );

        this.withMi = withMi;
    }

    @Override
    public void execute(PrintStream out, CommandLine cmdLine) {

        if (cmdLine.getArgList().size() != 1) {
            executeTarget(out);
        } else {
            // get the file we want to send
            int fileToDeliverNumber;

            try {
                fileToDeliverNumber = Integer.parseInt(cmdLine.getArgList().get(0).trim());
            } catch (NumberFormatException e) {
                out.println("Argument was not a valid number: " + cmdLine.getArgList().get(0));
                return;
            }

            // List<File> files = withMi.obtainFiles();

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

            if ((fileToDeliverNumber < 0) || (fileToDeliverNumber >= sortedFiles.size())) {
                executeGateKeeper(out, fileToDeliverNumber);
                return;
            }

            File fileToDeliver = sortedFiles.get(fileToDeliverNumber);

            try {
                FileTransfer sender = new FileTransferBuilder().setWithMi(withMi).createFileTransfer();
                sender.deliverZlib(SENDING, fileToDeliver);
                out.println(fileToDeliver.getName() + " sent");
            } catch (Exception e) {
                out.println("Could not send file: " + e.getMessage());
            }
        }
    }

    private void executeGateKeeper(PrintStream out, int fileToDeliverNumber) {
        out.println("Invalid file number: " + fileToDeliverNumber);
        return;
    }

    private void executeTarget(PrintStream out) {
        out.println(USAGE);
        out.println("The command 'availablefiles' will show the files you may send along with their file numbers");
    }
}
