package battleboats_1.com.cyberpointllc.stac.host;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersEmpty;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;


public class StacMain {


    public static void main(String args[]) throws Throwable {
        Options options = new Options();
        options.addOption("i", true, "Path to comms id file for this user");
        CommandLineParser grabber = new DefaultParser();

        try{
            TalkersEmpty empty = null;
            CommandLine cmd = grabber.parse(options,args);
            if(cmd.hasOption("i")){
                String id = cmd.getOptionValue("i");
                empty = TalkersEmpty.loadFromFile(new File(id));
                System.err.println("Loaded id: " + empty);
            } else{
                System.err.println("must specify id file -i");
                HelpFormatter formatter = new HelpFormatter();
                formatter.printHelp("<options>", options);
                System.exit(1);
            }
            WarShips warShips = new WarShips(empty);
            warShips.run();

        }
        catch(ParseException ex){
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("<options>", options);
            System.err.println("Parsing failed. Reason: " + ex);
            System.exit(1);
        }



















    }

}
