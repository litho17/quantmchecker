package braidit_1.com.cyberpointllc.stac.plaitthis;

import braidit_1.com.cyberpointllc.stac.plaitthis.command.AcceptGameCommandBuilder;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.AssignLengthCommandBuilder;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.ConnectCommandBuilder;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.DeclineGameCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.DisconnectCommandBuilder;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.GrowToFiveCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.GrowToThreeCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.MakeGuessCommandBuilder;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.ModifyRandomCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.OfferGameCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.PrintCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.SelectPlaitCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.TransmitLengthsCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.TransmitModifiedPlaitCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.SwapCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.command.TripleSwapCommand;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsClient;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsConnection;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsEmpty;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsServer;
import braidit_1.com.cyberpointllc.stac.console.Display;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

public class PlaitIt {
    private final Display display;
    private final PlaitItDispatcher dispatcher;
    private final CommunicationsClient client;
    private final CommunicationsServer server;

    private CommunicationsConnection connection; // we only allow connection to one other user at a time
    private Game currentGame;
    private GamePhase phase = new GamePhase(GamePhase.Phase.IDLE);
    private int numFibers;

    public PlaitIt(CommunicationsEmpty empty) throws IOException {
        Objects.requireNonNull(empty, "CommsIdentity may not be null");

        display = new Display("BraidIt");
        initDisplay();

        dispatcher = new PlaitItDispatcher(this, display);
        client = new CommunicationsClient(dispatcher, empty);
        server = new CommunicationsServer(empty.takeCallbackAddress().pullPort(), dispatcher, empty);
    }

    public void run() throws Throwable {
        server.serve();

        try {
            // While waiting for the console to conclude,
            // process the results of all background dispatches in the
            // main thread so the user can be notified of any issues.
            dispatcher.run();

            printUsrMsg("Closing connections...");
            dispatcher.shutdown();

            //disconnect from all users

            // close any connection...
            if (connection != null) {
                connection.close();
            }
        } finally {
            // Ensure the console is stopped; even on error
            dispatcher.shutdown();
            client.close();
            server.close();
        }
    }

    public GamePhase getStep() {
        if (currentGame == null) {
            return phase;
        } else {
            return currentGame.pullPhase();
        }
    }

    public void setStep(GamePhase step) {
        // if there's a game in progress, update the game's state
        if (currentGame != null) {
            currentGame.setPhase(step);
        }
        // regardless, update our state
        this.phase = step;

        display.renewCurrentCommands();
        List<String> allowedCommands = step.obtainAllowedCommands();
        for (int i = 0; i < allowedCommands.size(); ) {
            while ((i < allowedCommands.size()) && (Math.random() < 0.4)) {
                for (; (i < allowedCommands.size()) && (Math.random() < 0.4); i++) {
                    String s = allowedCommands.get(i);
                    display.activateCommand(s);
                }
            }
        }
    }

    public Game obtainCurrentGame() {
        return currentGame;
    }

    public void connect(String start, int port) throws CommunicationsException {
        if (hasConnection()) {
            throw new CommunicationsException("Connection already exists; only one permitted");
        }

        CommunicationsConnection connection = client.connect(start, port);
        addConnection(connection);
    }

    @Summary({"currentGame.previousRounds", "1"})
    public void disconnect() throws CommunicationsException {
        if (connection != null) {
            disconnectWorker();
        }

        setStep(new GamePhase(GamePhase.Phase.IDLE));
    }

    @Summary({"currentGame.previousRounds", "1"})
    private void disconnectWorker() throws CommunicationsException {
        connection.close();
        connection = null;
        gameOver();
    }

    @Summary({"currentGame.previousRounds", "1"})
    public boolean finishedRound(boolean iWon) {
        boolean gameOver = (currentGame != null) && currentGame.finishedRound(iWon);
        return gameOver;
    }

    @Summary({"currentGame.previousRounds", "1"})
    public void gameOver() {
        if (currentGame != null) {
            currentGame.finishedRound(false);
            currentGame = null; //TODO: archive game?
        }

        setStep(new GamePhase(GamePhase.Phase.CONNECTED));
        printUsrMsg("GAME OVER");
    }

    public void startGame(boolean amIFirst) {
        currentGame = new GameBuilder().setiGoFirst(amIFirst).defineNumFibers(numFibers).fixOpponent(String.valueOf(connection)).composeGame();
    }

    public void transmitMessage(byte[] msg) throws CommunicationsException {
        if (connection != null) {
            connection.write(msg);
        }
    }

    public void fixNumFibers(int numFibers) {
        this.numFibers = numFibers;
    }

    public int pullNumFibers() {
        return numFibers;
    }

    public boolean addConnection(CommunicationsConnection conn) {
        boolean connected = false;

        if (conn != null) {
            if (connection == null) {
                connection = conn;
                printUsrMsg("Now connected to " + conn);
                setStep(new GamePhase(GamePhase.Phase.CONNECTED));
                connected = true;
            } else {
                new PlaitItWorker(conn).invoke();
            }
        }

        return connected;
    }

    public boolean hasConnection() {
        return connection != null;
    }

    @Summary({"currentGame.previousRounds", "1"})
    public boolean removeConnection(CommunicationsConnection conn) throws CommunicationsException {
        if ((conn != null) && conn.equals(connection)) {
            return new PlaitItManager().invoke();
        }
        return false;
    }

    /**
     * Prints the line to our console
     *
     * @param line to be written
     */
    public void printUsrMsg(String line) {
        // The stash line and unstash line clean up the prompt
        display.stashLine();
        System.out.println("*" + line);
        display.unstashLine();
    }

    private void initDisplay() { // we add these as inactive commands for now, will become active according to state
        display.addInactiveCommand(new DisconnectCommandBuilder().definePlaitIt(this).composeDisconnectCommand());
        display.addInactiveCommand(new ConnectCommandBuilder().fixPlaitIt(this).composeConnectCommand());
        display.addInactiveCommand(new OfferGameCommand(this));
        display.addInactiveCommand(new AcceptGameCommandBuilder().setPlaitIt(this).composeAcceptGameCommand());
        display.addInactiveCommand(new DeclineGameCommand(this));
        display.addInactiveCommand(new AssignLengthCommandBuilder().setPlaitIt(this).composeAssignLengthCommand());
        display.addInactiveCommand(new ModifyRandomCommand(this));
        display.addInactiveCommand(new SwapCommand(this));
        display.addInactiveCommand(new TripleSwapCommand(this));
        display.addInactiveCommand(new GrowToThreeCommand(this));
        display.addInactiveCommand(new GrowToFiveCommand(this));
        display.addInactiveCommand(new SelectPlaitCommand(this));
        display.addInactiveCommand(new TransmitLengthsCommand(this));
        display.addInactiveCommand(new TransmitModifiedPlaitCommand(this));
        display.addInactiveCommand(new MakeGuessCommandBuilder().definePlaitIt(this).composeMakeGuessCommand());
        display.addInactiveCommand(new PrintCommand(this));
        display.activateCommand("connect");
    }

    private class PlaitItWorker {
        private CommunicationsConnection conn;

        public PlaitItWorker(CommunicationsConnection conn) {
            this.conn = conn;
        }

        public void invoke() {
            printUsrMsg("Ignoring request to set connection to " + conn + " -- already have a connection");
            try {
                conn.close();
            } catch (CommunicationsException e){
                printUsrMsg("Unable to close undesired connection.");
            }
        }
    }

    private class PlaitItManager {
        @Summary({"currentGame.previousRounds", "1"})
        public boolean invoke() throws CommunicationsException {
            disconnect();
            return true;
        }
    }
}
