package battleboats_1.com.cyberpointllc.stac.battleship;

import battleboats_1.com.cyberpointllc.stac.battleship.commands.AcceptCompetitionCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.ConnectCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.DeclareFireCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.DeclineCompetitionCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.DisconnectCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.EndPlacingShipsCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.FireHelpCommandProducer;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.OfferCompetitionCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.LayShipCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.LayCannonCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.PrintBoardCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.commands.RandomlyDefineBoardCommand;
import battleboats_1.com.cyberpointllc.stac.battleship.stages.Stage;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersClient;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersConnection;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersEmpty;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersServer;
import battleboats_1.com.cyberpointllc.stac.command.Console;
import battleboats_1.com.cyberpointllc.stac.proto.Battleboats.Hit;

import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class WarShips {
    public static final int BOARD_SIZE_MINIMUM = 10;
    public static final int BOARD_SIZE_MAXIMUM = 20;
    public static final double SQUARE_SIZE_MINIMUM = 1;
    public static final double SQUARE_SIZE_MAXIMUM = 10;
    public static final int DIVISOR_MINIMUM = 1;
    public static final int DIVISOR_MAXIMUM = 15;

    private final Console console;
    private final WarShipsDispatcher dispatcher;
    private final TalkersClient client;
    private final TalkersServer server;

    private Competition currentCompetition;
    private TalkersConnection connection; // we only allow connection to one other user at a time
    private Stage previousStage;
    private Stage stage;
    private boolean amIFirst;

    private int boardSize;
    private double squareSize;
    private int divisors;

    public WarShips(TalkersEmpty empty) throws IOException {
        Objects.requireNonNull(empty, "CommsIdentity may not be null");

        console = new Console("BattleBoats");
        initConsole();
        assignStage(Stage.IDLE);

        dispatcher = new WarShipsDispatcher(this, console);
        client = new TalkersClient(dispatcher, empty);
        server = new TalkersServer(empty.obtainCallbackAddress().fetchPort(), dispatcher, empty);
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

            // close any connection...
            if (connection != null) {
                connection.close();
            }
        } finally {
            // Ensure the console is stopped; even on error
            if (dispatcher != null) {
                dispatcher.shutdown();
            }
            client.close();
            server.close();
        }
    }

    public void setCompetitionParameters(int boardSize, double squareSize, int divisors) {
        if ((boardSize < BOARD_SIZE_MINIMUM) || (boardSize > BOARD_SIZE_MAXIMUM)) {
            throw new IllegalArgumentException("BoardSize is outside the range [" + BOARD_SIZE_MINIMUM + ", " + BOARD_SIZE_MAXIMUM + "]: " + boardSize);
        }

        if ((squareSize < SQUARE_SIZE_MINIMUM) || (squareSize > SQUARE_SIZE_MAXIMUM)) {
            throw new IllegalArgumentException("SquareSize is outside the range [" + SQUARE_SIZE_MINIMUM + ", " + SQUARE_SIZE_MAXIMUM + "]: " + squareSize);
        }

        if ((divisors < DIVISOR_MINIMUM) || (divisors > DIVISOR_MAXIMUM)) {
            throw new IllegalArgumentException("Divisor size is outside the range [" + DIVISOR_MINIMUM + ", " + DIVISOR_MAXIMUM + "]: " + divisors);
        }

        this.boardSize = boardSize;
        this.squareSize = squareSize;
        this.divisors = divisors;
    }

    public int pullBoardSize() {
        return boardSize;
    }

    public Map<Square, Pin> fireTaken(String heightInMeters,
                                      String speedInMetersPerSecond,
                                      String elevationInDegrees,
                                      String boardAngleInDegrees) throws IllegalArgumentException {
        Map<Square, Pin> strikes = currentCompetition.fetchStrikeSquares(heightInMeters, speedInMetersPerSecond, elevationInDegrees, boardAngleInDegrees);
        return strikes;
    }

    /**
     * Prints the line to our console
     *
     * @param line to be written
     */
    public void printUsrMsg(String line) {
        // The stash line and unstash line clean up the prompt
        console.stashLine();
        System.out.println("*" + line);
        console.unstashLine();
    }

    public boolean addConnection(TalkersConnection conn) {
        boolean connected = false;

        if (conn != null) {
            if (connection == null) {
                connection = conn;
                printUsrMsg("Now connected to " + conn);
                assignStage(Stage.CONNECTED);
                connected = true;
            } else {
                printUsrMsg("Ignoring request to set connection to " + conn + " -- already have a connection");
                try {
                    conn.close();
                } catch (TalkersDeviation e) {
                    printUsrMsg("Unable to close undesired connection.");
                }
            }
        }

        return connected;
    }

    public boolean hasConnection() {
        return connection != null;
    }

    public boolean removeConnection(TalkersConnection conn) throws TalkersDeviation {
        if ((conn != null) && conn.equals(connection)) {
            disconnect();
            return true;
        }
        return false;
    }

    public void connect(String home, int port) throws TalkersDeviation {
        if (hasConnection()) {
            throw new TalkersDeviation("Connection already exists; only one permitted at a time");
        }
        TalkersConnection connection = client.connect(home, port);
        addConnection(connection);
    }

    public void sendMessage(byte[] msg) throws TalkersDeviation {
        if (connection != null) {
            connection.write(msg);
        }
    }

    public void startCompetition(boolean amIFirst) {
        currentCompetition = new Competition(boardSize, squareSize, divisors);
        this.amIFirst = amIFirst;
    }

    public void printOcean(Writer writer) {
        currentCompetition.printOceanBoard(writer);
    }

    public void printRadar(Writer writer) {
        currentCompetition.printRadarBoard(writer);
    }

    public boolean amIFirst() {
        return amIFirst;
    }

    protected void competitionOver() {
        if (currentCompetition != null) {
            competitionOverAssist();
        }
        currentCompetition = null;
        assignStage(Stage.CONNECTED);
    }

    private void competitionOverAssist() {
        currentCompetition.endCompetition();
        printUsrMsg("Game Over");
    }

    public void disconnect() throws TalkersDeviation {
        if (connection != null) {
            disconnectHelp();
        }

        assignStage(Stage.IDLE);
    }

    private void disconnectHelp() throws TalkersDeviation {
        connection.close();
        connection = null;
        competitionOver();
    }

    public String defineShip(String name, int length, int x, int y, String direction) {
        return currentCompetition.assignShip(name, length, x, y, direction);
    }

    public boolean setCannon(int x, int y) {
        return currentCompetition.assignCannon(x, y);
    }

    public Stage pullStage() {
        return stage;
    }

    public void assignStage(Stage stage) {
        this.previousStage = this.stage;
        this.stage = stage;

        console.releaseCurrentCommands();
        List<String> commands = stage.takeCommands();
        for (int p = 0; p < commands.size(); p++) {
            String s = commands.get(p);
            console.activateCommand(s);
        }
    }

    public void revertStage() {
        if (previousStage != null) {
            assignStage(previousStage);
            previousStage = null; // once we've reverted, we shouldn't revert further until the game has moved forward
        }
    }

    public void defineUpCompetition() {
        currentCompetition.setUpCompetition();
    }

    public boolean areAllShipsPlaced() {
        return currentCompetition.areAllShipsPlaced();
    }

    public String getPlacementMessage() {
        if (currentCompetition != null) {
            String msg = currentCompetition.getPlacementMessage();
            return rarefy(msg);
        }
        return " ";
    }

    public void setStrikeReports(List<Hit> strikes) {
        if (!currentCompetition.isOver()) {
            defineStrikeReportsTarget(strikes);
        }
    }

    private void defineStrikeReportsTarget(List<Hit> strikes) {
        Map<Square, Pin> squaresStrike = new HashMap<>();
        strikes.forEach(strike -> {
            int x = strike.getX();
            int y = strike.getY();
            Pin pin = Pin.fromName(strike.getPeg());
            if (pin != null) {
                if ((pin == Pin.MISS) || (pin == Pin.STRIKE)) {
                    printUsrMsg("X: " + x + " Y: " + y + " is a " + pin.takeName());
                } else {
                    printUsrMsg("X: " + x + " Y: " + y + " sunk the " + pin.takeName());
                }
                squaresStrike.put(new Square(x, y), pin);
            }

        });
        assignHitonRadar(squaresStrike);
    }

    public void showStrikeReports(Map<Square, Pin> radarStrikes) {
        Square cannon = currentCompetition.pullCannon();
        int strikesMade = 0;

        if (cannon != null) {
            for (Square sq : radarStrikes.keySet()) {
                Pin pin = radarStrikes.get(sq);
                int pixelX = sq.fetchX() + cannon.fetchX();
                int pixelY = sq.obtainY() + cannon.obtainY();

                if ((pixelX == 0) && (pixelY == 0)) {
                    printUsrMsg("Shot hit the cannon: a Miss");
                } else if (isOnBoard(pixelX) && isOnBoard(pixelY)) {
                    if ((pin == Pin.MISS) || (pin == Pin.STRIKE)) {
                        if (pin == Pin.STRIKE) {
                            strikesMade++;
                        }
                        printUsrMsg("X: " + pixelX + " Y: " + pixelY + " is a " + pin.takeName());
                    } else {
                        strikesMade++;
                        printUsrMsg("X: " + pixelX + " Y: " + pixelY + " sunk the " + pin.takeName());
                    }
                } else {
                    printUsrMsg("X: " + pixelX + " Y: " + pixelY + " was off the board: a Miss");
                }
            }
        }

        printUsrMsg("A total of " + strikesMade + " boat positions were hit");
    }

    private boolean isOnBoard(int pixel) {
        return ((pixel > 0) && (pixel <= boardSize));
    }

    public String rarefy(String s) {
        return Integer.toString(s.length());
    }

    public void assignHitonRadar(Map<Square, Pin> strikes) {
        if (!currentCompetition.isOver()) {
            currentCompetition.fixStrikeOnRadar(strikes);
        }
    }

    public boolean iWon() {
        return currentCompetition.iWon();
    }

    private void initConsole() {
        console.addInactiveCommand(new PrintBoardCommand(this));

        console.addInactiveCommand(new ConnectCommand(this));
        console.addInactiveCommand(new DisconnectCommand(this));

        console.addInactiveCommand(new OfferCompetitionCommand(this));
        console.addInactiveCommand(new AcceptCompetitionCommand(this));
        console.addInactiveCommand(new DeclineCompetitionCommand(this));

        console.addInactiveCommand(new LayShipCommand(this, Pin.CARRIER.takeName(), Pin.CARRIER.getLength()));
        console.addInactiveCommand(new LayShipCommand(this, Pin.BATTLESHIP.takeName(), Pin.BATTLESHIP.getLength()));
        console.addInactiveCommand(new LayShipCommand(this, Pin.CRUISER.takeName(), Pin.CRUISER.getLength()));
        console.addInactiveCommand(new LayShipCommand(this, Pin.SUBMARINE.takeName(), Pin.SUBMARINE.getLength()));
        console.addInactiveCommand(new LayShipCommand(this, Pin.DESTROYER.takeName(), Pin.DESTROYER.getLength()));
        console.addInactiveCommand(new RandomlyDefineBoardCommand(this));
        console.addInactiveCommand(new LayCannonCommand(this));
        console.addInactiveCommand(new EndPlacingShipsCommand(this));
        console.addInactiveCommand(new DeclareFireCommand(this));
        console.addInactiveCommand(new FireHelpCommandProducer().fixWarShips(this).makeFireHelpCommand());
    }

    public double pullSquareSize() {
        return squareSize;
    }
}
