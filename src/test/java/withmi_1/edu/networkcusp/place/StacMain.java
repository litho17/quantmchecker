package withmi_1.edu.networkcusp.place;

import plv.colorado.edu.quantmchecker.qual.Inv;
import withmi_1.edu.networkcusp.protocols.CommunicationsIdentity;
import withmi_1.edu.networkcusp.chatbox.HangIn;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import withmi_1.edu.networkcusp.terminal.*;

import java.io.File;

public class StacMain {

    public static void main(String[] args) {
        Options options = new Options();
        CommandLineParser parser = new DefaultParser();
        options.addOption("i", true, "Path to the id file");
        options.addOption("d", true, "Path to the data folder");
        options.addOption("s", true, "Path to the storage folder");

        try {
            CommunicationsIdentity identity = null;
            CommandLine cmd = parser.parse(options, args);

            if (cmd.hasOption("i")) {
                String idFilePath = cmd.getOptionValue("i");
                identity = CommunicationsIdentity.loadFromFile(new File(idFilePath));
                System.err.println("Using identity: " + identity);
            } else {
                System.err.println("must specify id file at command line with -i");
                HelpFormatter formatter = new HelpFormatter();
                formatter.printHelp("withmi <options>", options);
                System.exit(1);
            }

            String dataRootPath = cmd.getOptionValue("d", "data");
            String dataDirPath = dataRootPath + "/files";
            File dataDirectory = new File(dataDirPath);
            if (!dataDirectory.exists()) {
                dataDirectory.mkdirs();
            }

            String memberStorageDirPath = cmd.getOptionValue("s", "incoming");
            File memberStorageDir = new File(memberStorageDirPath);
            if (!memberStorageDir.exists()) {
                mainHelper(memberStorageDir);
            }

            System.out.println("Listening on port " + identity.pullCallbackAddress().pullPort());

            @Inv("= discussion.console.commands (+ c56 c57 c58 c59 c60)") HangIn discussion = new HangIn(identity, dataDirectory, memberStorageDir);
            c56: discussion.console.addCommand(new ExitCommand(discussion.console));
            c57: discussion.console.addCommand(new HelpCommand(discussion.console));
            c58: discussion.console.addCommand(new RepeatCommand(discussion.console));
            c59: discussion.console.addCommand(new HistoryCommand(discussion.console));
            c60: discussion.console.addCommand(new ScriptCommand(discussion.console));
            discussion.run();
            System.exit(0);
        } catch (ParseException e) {
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("withmi <options>", options);
            // oops, something went wrong
            System.err.println("Parsing failed.  Reason: " + e.getMessage());
            System.exit(1);
        } catch (Throwable e) {
            System.err.println(e);
            System.exit(1);
        }
    }

    private static void mainHelper(File memberStorageDir) {
        new StacMainEntity(memberStorageDir).invoke();
    }

    private static class StacMainEntity {
        private File memberStorageDir;

        public StacMainEntity(File memberStorageDir) {
            this.memberStorageDir = memberStorageDir;
        }

        public void invoke() {
            memberStorageDir.mkdirs();
        }
    }
}
