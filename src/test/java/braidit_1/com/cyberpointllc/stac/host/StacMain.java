package braidit_1.com.cyberpointllc.stac.host;

import braidit_1.com.cyberpointllc.stac.plait.Plait;
import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsEmpty;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;

public class StacMain{

    public static void main(String[] args) throws Throwable{
        Options options = new Options();
        options.addOption("i", true, "For running the game: path to comms id file for this user");
        options.addOption("b1", true, "For standalone braid comparison: first braid to compare");
        options.addOption("b2", true, "For standalone braid comparison: second braid to compare");
        CommandLineParser parser = new DefaultParser();

        try{
            CommunicationsEmpty empty = null;
            CommandLine cmd = parser.parse(options, args);

            // b1 and b2 option is just for comparing two braids
            if (cmd.hasOption("b1") && cmd.hasOption("b2")){
                new StacMainHome(cmd).invoke();
            }
            // to run the actual client, use option i with id file
            else if (cmd.hasOption("i")){
                String id = cmd.getOptionValue("i");
                empty = CommunicationsEmpty.loadFromFile(new File(id));
                System.err.println("Loaded id: " + empty);
                PlaitIt plaitIt = new PlaitIt(empty);
                plaitIt.run();
            } else {
                new StacMainAid(options).invoke();
            }


        } catch (ParseException ex){
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("<options>", options);
            System.err.println("Parsing failed.  Reason: " + ex.getMessage());
            System.exit(1);
        }
    }

    private static class StacMainHome {
        private CommandLine cmd;

        public StacMainHome(CommandLine cmd) {
            this.cmd = cmd;
        }

        public void invoke() {
            String s1 = cmd.getOptionValue("b1");
            String s2 = cmd.getOptionValue("b2");
            Plait b1 = new Plait(s1, Plait.MAX_FIBERS);
            Plait b2 = new Plait(s2, Plait.MAX_FIBERS);
            if (b1.isEquivalent(b2)){
                System.out.println("Braids are equivalent");
            } else {
                System.out.println("Braids are NOT equivalent");
            }
        }
    }

    private static class StacMainAid {
        private Options options;

        public StacMainAid(Options options) {
            this.options = options;
        }

        public void invoke() {
            System.err.println("If not running in standalone mode, must specify id file -i");
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("<options>", options);
            System.exit(1);
        }
    }
}