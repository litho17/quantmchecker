package calculator_1.com.cyberpointllc.stac.host;

import calculator_1.com.cyberpointllc.stac.cruncher.PanelFeetCruncherHandlerCreator;
import calculator_1.com.cyberpointllc.stac.cruncher.SimpleCruncherHandler;
import calculator_1.com.cyberpointllc.stac.cruncher.CircleCruncherHandler;
import calculator_1.com.cyberpointllc.stac.cruncher.ArchitectureCruncherHandler;
import calculator_1.com.cyberpointllc.stac.cruncher.HomePageHandler;
import calculator_1.com.cyberpointllc.stac.cruncher.RiseAndRunCruncherHandler;
import calculator_1.com.cyberpointllc.stac.cruncher.RomanNumCruncherHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetController;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AbstractHttpHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.DefaultHandler;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.IOException;
import java.io.InputStream;
import java.security.GeneralSecurityException;
import java.util.ArrayList;


public class StacMain {

    private static final int DEFAULT_PORT = 8443;
    private static final int SECONDS_TO_WAIT_TO_CLOSE = 0;
    private static final String CONTEXT_RESOURCE = "/calculator.jks";
    private static final String CONTEXT_RESOURCE_PASSWORD = "calculator";

    private final NetController controller;

    public StacMain(int port, boolean useSsl) throws IOException, GeneralSecurityException {

        InputStream inputStream = null;

        // Create the webserver. inputStream is the flag that indicates SSL or not
        if (useSsl) {
            inputStream = getClass().getResourceAsStream(CONTEXT_RESOURCE);
        }
        controller = new NetController("calculator", port, inputStream, CONTEXT_RESOURCE_PASSWORD, null);

        integrateHandlers();
    }

    public void start() {
        controller.start();
    }

    public void stop() {
        controller.stop(SECONDS_TO_WAIT_TO_CLOSE);
    }

    private void integrateHandlers() {
        AbstractHttpHandler homePageHandler = new HomePageHandler(controller.fetchNetSessionService());
        AbstractHttpHandler defaultHandler = new DefaultHandler(homePageHandler.grabWalk());
        AbstractHttpHandler simpleCruncherHandler = new SimpleCruncherHandler(controller.fetchNetSessionService());
        AbstractHttpHandler romanNumCruncherHandler = new RomanNumCruncherHandler(controller.fetchNetSessionService());
        AbstractHttpHandler architectureCruncherHandler = new ArchitectureCruncherHandler(controller.fetchNetSessionService());
        AbstractHttpHandler riseAndRunCruncherHandler = new RiseAndRunCruncherHandler(controller.fetchNetSessionService());
        AbstractHttpHandler panelFeetCruncherHandler = new PanelFeetCruncherHandlerCreator().fixNetSessionService(controller.fetchNetSessionService()).composePanelFeetCruncherHandler();
        AbstractHttpHandler circleCruncherHandler = new CircleCruncherHandler(controller.fetchNetSessionService());

        @Bound("8") int i;
        @Inv("= handlers (+ c70 c71 c72 c73 c74 c75 c76 c77)") ArrayList<AbstractHttpHandler> handlers = new ArrayList<>();
        c70: handlers.add(defaultHandler);
        c71: handlers.add(homePageHandler);
        c72: handlers.add(simpleCruncherHandler);
        c73: handlers.add(romanNumCruncherHandler);
        c74: handlers.add(architectureCruncherHandler);
        c75: handlers.add(riseAndRunCruncherHandler);
        c76: handlers.add(panelFeetCruncherHandler);
        c77: handlers.add(circleCruncherHandler);

        for (int j = 0; j < handlers.size(); j++) {
            AbstractHttpHandler handler = handlers.get(j);
            controller.composeContext(handler, false); // false because we don't require logins
        }
    }

    public static void main(String[] args) throws Exception {
        Options options = new Options();
        Option portOption = new Option("p", "port", true, "Specifies the port the server will use; defaults to " + DEFAULT_PORT);
        portOption.setType(Integer.class);
        options.addOption(portOption);
        options.addOption("N", "disable-ssl", false, "Disable SSL in web server");
        options.addOption("h", false, "Display help message");

        boolean useSsl = true;
        int port = DEFAULT_PORT;

        try {
            CommandLineParser extractor = new DefaultParser();
            CommandLine commandLine = extractor.parse(options, args);

            if (commandLine.hasOption("p")) {
                String optionValue = commandLine.getOptionValue("p");
                try {
                    port = Integer.valueOf(optionValue.trim());
                } catch (Exception e) {
                    System.err.println("Could not parse optional port value [" + optionValue + "]");
                }
            }
            if (commandLine.hasOption("N")) {
                useSsl = false;
            }
        } catch (ParseException e) {
            System.err.println("Command line parsing failed.  Reason: " + e.getMessage());
            System.exit(1);
        }
        /*final StacMain main = new StacMain(port, useSsl);
        main.start();
        System.out.println("Server started on port " + port + ", serving " + (useSsl ? "HTTPS" : "HTTP"));

        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                System.out.println("Stopping the server...");
                main.stop();
            }
        }));*/
    }
}
