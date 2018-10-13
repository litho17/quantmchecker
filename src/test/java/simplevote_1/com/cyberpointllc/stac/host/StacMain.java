package simplevote_1.com.cyberpointllc.stac.host;

import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteServiceRealization;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.basicvote.accumulation.CompilationService;
import simplevote_1.com.cyberpointllc.stac.basicvote.accumulation.CompilationChore;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.AdminGuide;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.ConfirmationGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.EditBallotGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.IconGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.PermissionAssessGuide;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.PermissionAssessGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.PermissionKeyRarefy;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.OutcomesGuide;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.ShowResponsesGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.ShowSurveysGuide;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.DirectVoteHelper;
import simplevote_1.com.cyberpointllc.stac.basicvote.handler.VoterGuideCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.save.MapDBStorageService;
import simplevote_1.com.cyberpointllc.stac.webmaster.PersonConductor;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkServer;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.AbstractHttpGuide;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.DefaultGuide;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.DefaultGuideCreator;
import com.sun.net.httpserver.HttpContext;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

public class StacMain {
    private static final int DEFAULT_PORT = 8443;
    private static final String MAPDB_FILE = "stac.db";
    private static final int SECONDS_TO_WAIT_TO_CLOSE = 0;
    private static final String CONTEXT_RESOURCE = "/simplevote.jks";
    private static final String CONTEXT_RESOURCE_PASSWORD = "simplevote";
    private static final long COMPILATION_DELAY_MINUTES = 60;
    private static final long COMPILATION_INTERVAL_MINUTES = 60;

    private final PersonConductor personConductor;
    private final NetworkServer server;
    private final ScheduledExecutorService scheduler;
    private CompilationService compilationService;

    public static void main(String args[]) throws Exception {
        Options options = new Options();
        Option portOption = new Option("p", "port", true, "Specifies the port the server will use; defaults to " + DEFAULT_PORT);
        portOption.setType(Integer.class);
        options.addOption(portOption);
        options.addOption("d", "datapath", true, "Path to the existing data storage directory");
        options.addOption("i", "commsIdFile", true, "File containing comms identity for this server");
        options.addOption("s", "serverlist", true, "File containing a list of other servers to connect to");
        options.addOption("r", "rebuild", false, "Removes any existing persistence and reloads initial model data");
        options.addOption("w", "passwordkey", true, "File containing a key used to encrypt passwords");
        options.addOption("h", false, "Display this help message");

        int port = DEFAULT_PORT;
        String dataTrail = null;
        String serverListTrail = null;
        String protocolsIdTrail = null;
        boolean rebuildDB = false;
        String passwordKeyTrail = null;

        try {
            CommandLineParser parser = new DefaultParser();
            CommandLine commandLine = parser.parse(options, args);

            if (commandLine.hasOption("p")) {
                String optionEssence = commandLine.getOptionValue("p");
                try {
                    port = Integer.valueOf(optionEssence.trim());
                } catch (Exception e) {
                    System.err.println("Could not parse optional port value [" + optionEssence + "]");
                }
            }

            if (commandLine.hasOption("d")) {
                dataTrail = commandLine.getOptionValue("d");
            }

            if (commandLine.hasOption("i")) {
                protocolsIdTrail = commandLine.getOptionValue("i");
            }

            if (commandLine.hasOption("s")) {
                serverListTrail = commandLine.getOptionValue("s");
            }

            if (commandLine.hasOption("r")) {
                rebuildDB = true;
            }

            if (commandLine.hasOption("w")) {
                passwordKeyTrail = commandLine.getOptionValue("w");
            }

            if (commandLine.hasOption("h")) {
                mainUtility(options);
            }
        } catch (ParseException e) {
            System.err.println("Command line parsing failed.  Reason: " + e.getMessage());
            System.exit(1);
        }

        if (dataTrail == null) {
            mainExecutor();
        }

        // Make sure the directory to the data path exists
        File dataTrailParent = new File(dataTrail);

        if (!dataTrailParent.exists() || !dataTrailParent.isDirectory() || !dataTrailParent.canWrite()) {
            System.err.println("ERROR: specified datapath " + dataTrail + " does not exist or is not a writeable directory");
            System.exit(1);
        }

        // make sure the comms id file exists
        if (protocolsIdTrail == null) {
            StacMainGateKeeper.invoke();
        }

        File protocolsIdFile = new File(protocolsIdTrail);

        if (!protocolsIdFile.exists()) {
            System.err.println("ERROR: specified comms id file " + protocolsIdFile + " does not exist");
            System.exit(1);
        }

        // make sure the server list file exists
        if (serverListTrail == null) {
            mainFunction();
        }

        File serverListFile = new File(serverListTrail);

        if (!serverListFile.exists()) {
            new StacMainCoordinator(serverListFile).invoke();
        }


        // Make sure the key path exists
        if (passwordKeyTrail == null) {
            mainGateKeeper();
        }

        File passwordKeyFile = new File(passwordKeyTrail);

        if (!passwordKeyFile.exists() || passwordKeyFile.isDirectory() || !passwordKeyFile.canRead()) {
            System.err.println("ERROR: specified password key " + passwordKeyFile + " does not exist, is a directory, or cannot be read");
            System.exit(1);
        }

        final StacMain main = new StacMain(port, dataTrailParent, passwordKeyFile, protocolsIdFile, serverListFile, rebuildDB);

        main.start();

        System.out.println("Server started on port " + port);
        main.startCompilationService();

        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                System.out.println("Stopping the server...");
                main.stop();
            }
        }));
    }

    private static void mainGateKeeper() {
        System.err.println("ERROR: a password key must be specified");
        System.exit(1);
    }

    private static void mainFunction() {
        System.err.println("ERROR: a server list file must be specified");
        System.exit(1);
    }

    private static void mainExecutor() {
        System.err.println("ERROR: a data path must be specified");
        System.exit(1);
    }

    private static void mainUtility(Options options) {
        HelpFormatter formatter = new HelpFormatter();
        formatter.printHelp("SimpleVote <options>", options);
        System.exit(0);
    }

    public StacMain(int port, File dataTrailParent, File passwordKeyFile, File protocolsIdFile, File serverListFile, boolean rebuild) throws Exception {
        String passwordKey = FileUtils.readFileToString(passwordKeyFile, Charset.forName("UTF-8"));

        MapDBStorageService storageService = getStorageService(dataTrailParent, rebuild, passwordKey);
        storageService.cleanDatabase();

        // Populate the user manager
        personConductor = new PersonConductor();

        compilationService = new CompilationService(protocolsIdFile, serverListFile);
        DirectVoteService directVoteService = new DirectVoteServiceRealization(storageService, compilationService);


        // task to periodically send election results between servers
        scheduler = Executors.newSingleThreadScheduledExecutor();
        CompilationChore chore = new CompilationChore(directVoteService, TimeUnit.MINUTES.toMillis(COMPILATION_INTERVAL_MINUTES), true);
        scheduler.scheduleWithFixedDelay(chore, COMPILATION_DELAY_MINUTES, COMPILATION_INTERVAL_MINUTES, TimeUnit.MINUTES);

        setupNightlyDatabaseClean(storageService, scheduler);


        for (Voter person : directVoteService.fetchVoters()) {
            personConductor.addPerson(person);
        }

        // Create the webserver...
        try (InputStream inputStream = getClass().getResourceAsStream(CONTEXT_RESOURCE)) {
            // Note: to encrypt stored passwords, replace null with passwordKeyFile)
            server = new NetworkServer("simplevote", port, inputStream, CONTEXT_RESOURCE_PASSWORD, null);
        }

        // Add the handlers (currently, there is no need for a default user id)
        addGuides(directVoteService, null);
    }

    public void start() {
        server.start();
    }

    public void stop() {
        scheduler.shutdown();
        server.stop(SECONDS_TO_WAIT_TO_CLOSE);
    }

    /**
     * Add all of the handlers to StacMain
     */
    private void addGuides(DirectVoteService directVoteService,
                           String defaultPersonId) {
        NetworkSessionService networkSessionService = server.takeNetworkSessionService();
        DirectVoteHelper directVoteHelper = new DirectVoteHelper(directVoteService, networkSessionService);

        ShowSurveysGuide showSurveysGuide = new ShowSurveysGuide(directVoteHelper);
        DefaultGuide defaultGuide = new DefaultGuideCreator().fixDefaultTrail(showSurveysGuide.takeTrail()).formDefaultGuide();

        PermissionAssessGuide permissionAssessGuide = new PermissionAssessGuideCreator().setDirectVoteHelper(directVoteHelper).formPermissionAssessGuide();

        List<AbstractHttpGuide> guides = new ArrayList<>();
        guides.add(showSurveysGuide);
        guides.add(defaultGuide);
        guides.add(permissionAssessGuide);
        guides.add(new VoterGuideCreator().assignDirectVoteHelper(directVoteHelper).formVoterGuide());

        guides.add(new OutcomesGuide(directVoteHelper));
        guides.add(new AdminGuide(directVoteHelper));

        if (defaultPersonId == null) {
            server.addAuthGuides(personConductor, defaultGuide.takeTrail());
        } else {
            server.addDefaultAuthGuides(personConductor, defaultPersonId);
        }

        // Add each handler that only requires authentication
        for (int b = 0; b < guides.size(); b++) {
            new StacMainUtility(guides, b).invoke();
        }

        // Build up the handler list that also needs a Registration Key
        guides.clear();
        guides.add(new EditBallotGuideCreator().assignDirectVoteHelper(directVoteHelper).formEditBallotGuide());
        guides.add(new ConfirmationGuideCreator().fixDirectVoteHelper(directVoteHelper).formConfirmationGuide());
        guides.add(new ShowResponsesGuideCreator().setDirectVoteHelper(directVoteHelper).formShowResponsesGuide());

        for (int b = 0; b < guides.size(); b++) {
            AbstractHttpGuide guide = guides.get(b);
            addPermissionGuide(directVoteHelper, permissionAssessGuide, guide);
        }

        // Add icon handler without authentication
        server.formContext(new IconGuideCreator().assignDirectVoteHelper(directVoteHelper).formIconGuide(), false);
    }

    private void startCompilationService() throws Exception {
        compilationService.start();
    }

    private void addPermissionGuide(DirectVoteHelper directVoteHelper,
                                    PermissionAssessGuide permissionAssessGuide,
                                    AbstractHttpGuide guide) {
        // Create a filter for verifying registration keys.
        // If the key is missing or is not valid,
        // the user is redirected to the registration key handler page.
        PermissionKeyRarefy permissionKeyRarefy = new PermissionKeyRarefy(
                directVoteHelper,
                guide.takeTrail(),
                permissionAssessGuide.takeTrail()
        );

        // Add the handler and require authentication AND
        // registration key validation
        HttpContext context = server.formContext(guide, true);
        context.getFilters().add(permissionKeyRarefy);
    }

    private MapDBStorageService getStorageService(File parent,
                                                  boolean rebuild,
                                                  String passwordKey) throws IOException {
        if (parent == null) {
            throw new IllegalArgumentException("Database parent File may not be null");
        }

        if (!parent.exists() || !parent.isDirectory() || !parent.canWrite()) {
            throw new IllegalArgumentException("Parent directory " + parent + " must exist, be a directory, and be writable");
        }

        File file = new File(parent, MAPDB_FILE);

        boolean populate = rebuild || !file.exists();

        if (file.exists() && rebuild) {
            if (!file.delete()) {
                throw new IllegalArgumentException("Existing File could not be deleted: " + file);
            }
        }

        MapDBStorageService storageService = new MapDBStorageService(file, passwordKey);

        if (populate) {
            // NOTE: if one wishes to encrypt stored passwords, replace null with passwordKey.
            DirectVoteLoader.populate(storageService, null, parent);
        }

        return storageService;
    }

    // task to remove invalid ballots nightly (11:59 pm)
    private void setupNightlyDatabaseClean(final MapDBStorageService storageService, ScheduledExecutorService scheduler) {
        Calendar calendar = Calendar.getInstance();
        Date now = calendar.getTime();
        // set calendar time to 11:59 pm
        calendar.set(Calendar.HOUR_OF_DAY, 23);
        calendar.set(Calendar.MINUTE, 59);
        long timeToMidnight = calendar.getTime().getTime() - now.getTime();
        scheduler.scheduleWithFixedDelay(storageService::cleanDatabase, timeToMidnight, TimeUnit.DAYS.toMillis(1), TimeUnit.MILLISECONDS);
    }

    private static class StacMainGateKeeper {
        private static void invoke() {
            System.err.println("ERROR: a comms id file must be specified");
            System.exit(1);
        }
    }

    private static class StacMainCoordinator {
        private File serverListFile;

        public StacMainCoordinator(File serverListFile) {
            this.serverListFile = serverListFile;
        }

        public void invoke() {
            System.err.println("ERROR: specified server list file " + serverListFile + " does not exist");
            System.exit(1);
        }
    }

    private class StacMainUtility {
        private List<AbstractHttpGuide> guides;
        private int c;

        public StacMainUtility(List<AbstractHttpGuide> guides, int c) {
            this.guides = guides;
            this.c = c;
        }

        public void invoke() {
            AbstractHttpGuide guide = guides.get(c);
            server.formContext(guide, true);
        }
    }
}
