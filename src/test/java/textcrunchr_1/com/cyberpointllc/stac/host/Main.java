/*
 * Textcrunchr main
 */
package textcrunchr_1.com.cyberpointllc.stac.host;

import org.apache.commons.cli.*;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.*;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

public class Main {

    /*
     * main
     */
    public static void main(String[] args) {
        mainHelper(args);
    }

    private static void mainHelper(String[] args) {
        Options options = new Options();
        String filename = "";
        String outputOption = "";
        String[] processors = new String[0];
        @InvUnk("Reassign") OutputHandler outph;
        try {
            CommandLineParser parser = new DefaultParser();
            options.addOption("o", true, "Output form. Defaults to console." + "\nUse either \"console\", \"xml\" or \"window\"");
            options.addOption("h", false, "Display this help message");
            Option processOption = new Option("p", "Processors. Defaults to running all Processors." + "\nPick from \"characterCount\", \"enigma\", \"languageAnalysis\", \"sentenceStats\", \"wordStats\", \"wordFreqs\"");
            processOption.setArgs(Option.UNLIMITED_VALUES);
            options.addOption(processOption);
            InputPathHandler ipHandler = new InputPathHandler();
            @Inv("= (* tfHandler.processors 5) c39") TextFileHandler tfHandler;
            c39: tfHandler = new TextFileHandler();
            try {
                CommandLine cmd = parser.parse(options, args);
                if (cmd.hasOption("p")) {
                    processors = cmd.getOptionValues("p");
                }
                if (cmd.hasOption("o")) {
                    outputOption = cmd.getOptionValue("o");
                } else if (cmd.hasOption("h")) {
                    HelpFormatter formatter = new HelpFormatter();
                    formatter.printHelp("TextCrunchr <options> <file>", options);
                    System.exit(0);
                }
                filename = cmd.getArgs()[0];
            } catch (ParseException exp) {
                System.err.println("Parsing failed.  Reason: " + exp.getMessage());
                System.exit(1);
            }
            List<String> files = ipHandler.handleInputPath(filename);
            outph = OutputHandlerFactory.getOutputHandler(outputOption);
            for (String filepath : files) {
                try {
                    @Inv("= argsList args") List<String> argsList = new ArrayList<String>(Arrays.asList(processors));
                    Iterator<Processor> it = tfHandler.processors.iterator();
                    while (it.hasNext()) {
                        Processor processor;
                        processor = it.next();
                        if (argsList.isEmpty() || argsList.contains(processor.getName())) {
                            @InvUnk("Dynamic dispatch") TCResult tcr = processor.process(new FileInputStream(filepath));
                            outph.addResult(filepath, tcr);
                        }
                    }
                } catch (IOException ioe) {
                    System.out.println("file " + filepath + " could not be analyzed.");
                    ioe.printStackTrace();
                }
            }
            // conclude and output
            try {
                outph.conclude();
            } catch (OutputHandlerException ohe) {
                System.out.println(ohe.toString());
            }
        } catch (Exception e) {
            e.printStackTrace();
            System.err.println("TextCrunchr has crashed.");
        }
    }
}
