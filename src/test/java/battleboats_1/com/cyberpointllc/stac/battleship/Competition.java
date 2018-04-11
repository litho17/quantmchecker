package battleboats_1.com.cyberpointllc.stac.battleship;

import java.io.PrintWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Competition {
    private static final int NUMBER_OF_SHIPS = Pin.obtainShips().length;

    private static final int WAIT_TIME = 30;
    private boolean competitionOver = false;

    private final int boardSize;

    private final RadarBoard radar;
    private final OceanBoard ocean;

    private final int numberOfShips;

    private final Map<String, List<Square>> placedShips;

    private Square cannonSquare;

    private final Object LOCK = new Object();

    public Competition(int boardSize, double squareSize, int divisors) {
        this.boardSize = boardSize;

        numberOfShips = NUMBER_OF_SHIPS;

        radar = new RadarBoard(boardSize, numberOfShips);
        ocean = new OceanBoard(boardSize, divisors, squareSize, this);

        placedShips = new HashMap<>();
    }


    /**
     * The boats have already been set.
     * Set up the ocean board to allow the game to start.
     */
    public void setUpCompetition() {
        if (!areAllShipsPlaced()) {
            throw new IllegalStateException("Ships and cannon must be positioned before game can be set up.");
        }

        List<Ship> ships = new ArrayList<>();

        for (String name : placedShips.keySet()) {
            ships.add(new Ship(name, placedShips.get(name)));
        }

        ocean.fixShipsAndCannon(ships, cannonSquare);
    }


    public int obtainNumberOfShips() {
        return numberOfShips;
    }

    /**
     * @param name      the ship's name
     * @param length    the length of the ship. number of squares
     * @param x         the starting x placement of the ship
     * @param y         the starting y placement of the ship
     * @param direction the direction for the rest of the boat's squares
     * @return true if it was successfully placed
     */
    public String assignShip(String name, int length, int x, int y, String direction) {
        String reason = "Successful";
        Boolean canDefineShip = true;
        List<Square> holdShip = null;

        if (placedShips.containsKey(name)) {
            // Save the previous value if they are resetting this boat
            holdShip = placedShips.remove(name);
        }

        List<Square> shipSquares = obtainShipSquares(length, x, y, direction, name);

        if (shipSquares.isEmpty()) {
            // Either there are off-board squares or a misspelled direction
            canDefineShip = false;
            reason = "The boat would be located off the board or in an invalid direction";
        }

        if (canDefineShip && (cannonSquare != null) && shipSquares.contains(cannonSquare)) {
            // They are trying to place the boat on the cannon
            canDefineShip = false;
            reason = "This boat would overlap with the cannon position";
        }

        if (canDefineShip) {
            for (int q = 0; q < shipSquares.size(); q++) {
                Square shipSquare = shipSquares.get(q);
                for (List<Square> squares : placedShips.values()) {
                    if (squares.contains(shipSquare)) {
                        // Another boat is in the way
                        canDefineShip = false;
                        reason = "This boat would overlap with another boat";
                    }
                }
            }
        }

        if (canDefineShip) {
            placedShips.put(name, shipSquares);
        } else if (holdShip != null) {
            placedShips.put(name, holdShip);
        }

        return reason;
    }

    /**
     * @param length    length of the boat (in squares)
     * @param x         starting x coordinate in squares. must be between 1 and board size
     * @param y         starting y coordinate in squares. must be between 1 and board size
     * @param direction direction the ship is going (up, down, left, or right)
     * @param name      the name of the boat being placed (so we can print a specific message)
     * @return List of squares that the user wants to place the ship. An empty list if
     * any of the squares are off the board.
     */
    private List<Square> obtainShipSquares(int length, int x, int y, String direction, String name) {
        List<Square> squares = new ArrayList<>();

        for (int size = length; size > 0; size--) {
            if (((x > 0) && (x <= boardSize)) && ((y > 0) && (y <= boardSize))) {
                squares.add(new Square(x, y));
            }

            // TODO: Create a direction enum and use as argument to method; early evaluation of illegal direction
            if (direction.equalsIgnoreCase("up")) {
                y++;
            } else if (direction.equalsIgnoreCase("down")) {
                y--;
            } else if (direction.equalsIgnoreCase("left")) {
                x--;
            } else if (direction.equalsIgnoreCase("right")) {
                x++;
            } else {
                //if the direction is wrong
                return new CompetitionService().invoke();
            }
        }

        if (squares.size() != length) {
            // Some squares are off the board so return an empty List
            squares.clear();
        } else {
            // TODO: This doesn't belong here; maybe better in place boat command?  In fact, if there are errors, this msg should NOT be printed
            System.out.println("The " + name + " has been placed in these squares: " + squares.toString());
        }

        return squares;
    }

    public Square pullCannon() {
        return cannonSquare;
    }

    /**
     * @param x x grid location to place the cannon
     * @param y y grid location to place the cannon
     * @return boolean true if the cannon was placed; false if off the board or it overlaps a boat
     */
    public boolean assignCannon(int x, int y) {
        cannonSquare = null;

        if (((x < 1) || (x > boardSize)) || ((y < 1) || (y > boardSize))) {
            //it's off the board
            return false;
        }

        Square square = new Square(x, y);
        for (List<Square> squares : placedShips.values()) {
            if (squares.contains(square)) {
                // Another boat is in the way
                return false;
            }
        }

        // If there is no boat or cannon in the way, it can be placed there.
        cannonSquare = square;
        return true;
    }

    public boolean areAllShipsPlaced() {
        return (cannonSquare != null) && (placedShips.size() == obtainNumberOfShips());
    }

    public String getPlacementMessage() {
        if (cannonSquare != null) {
            return "Boats and cannon have been placed" + cannonSquare.obtainEncoding();
        } else {
            return "Error: cannon location is null";
        }
    }

    public void fixStrikeOnRadar(Map<Square, Pin> strikes) {
        radar.layPins(strikes);
    }

    /**
     * Uses the hitLocator to find the squares that are hit on the players ocean board
     *
     * @param height        height of the cannon in meters
     * @param speed      velocity of the shot in meters/second
     * @param verticalAngle angle in radians vertically
     * @param boardAngle    angle in radians on the board with 0 in positive X direction; increasing counter-clockwise
     * @return Map of the squares (on the radar board) hit by the shot and their peg value
     */
    public Map<Square, Pin> fetchStrikeSquares(String height, String speed, String verticalAngle, String boardAngle) throws IllegalArgumentException {
        StrikeLocator strikesLocator = new StrikeLocator(ocean, height, speed, verticalAngle, boardAngle);
        if (strikesLocator.assessErrorMessage()) {
            return strikesLocator.calculateStrikeCoordinates();
        } else {
            throw new IllegalArgumentException(strikesLocator.pullErrorMessage());
        }
    }

    public void printRadarBoard(Writer writer) {
        PrintWriter printWriter;
        if (writer instanceof PrintWriter) {
            printWriter = (PrintWriter) writer;
        } else {
            printWriter = new PrintWriter(writer);
        }
        printWriter.println();
        for (int y = boardSize; y >= (-boardSize); y--) {
            printWriter.print(y + "\t");
            for (int x = (-boardSize); x <= boardSize; x++) {
                Square sq = new Square(x, y);
                printWriter.print("  ");
                if (radar.board.containsKey(sq)) {
                    Pin pin = radar.board.get(sq);
                    printWriter.print(pin.getSymbol());
                    //either hit, miss, or sunk
                } else {
                    //hasn't been hit yet then
                    printWriter.print(".");
                }
            }
            printWriter.println();
        }
        //for the x, it will be double since it goes from -length to length
        printWriter.print("\t");
        for (int x = (-boardSize); x <= (boardSize); x++) {
            if (x < 0 || x >= 10) {
                printWriter.print(" " + x);
            } else {
                printWriter.print("  " + x);
            }
        }
        printWriter.println();
        printWriter.println("Ships and their length:");
        printWriter.println("Carrier:5, Battleship:4, cRuiser:3, Submarine:3, Destroyer:2");
        printWriter.println("The Cannon is marked by an O");
        printWriter.println();
    }

    /**
     * prints the ocean board with the first letter of the name of the ship.
     * this is done here so you can see boats and cannon as they're placed
     */
    public void printOceanBoard(Writer w) {
        PrintWriter printWriter;
        if (w instanceof PrintWriter) {
            printWriter = (PrintWriter) w;
        } else {
            printWriter = new PrintWriter(w);
        }

        boolean shipSquare = false;
        String name = "";
        printWriter.println();
        for (int y = boardSize; y >= 1; ) {
            while ((y >= 1) && (Math.random() < 0.5)) {
                for (; (y >= 1) && (Math.random() < 0.4); y--) {
                    //prints the y (row) numbers
                    if (y < 10) {
                        printWriter.print(y + "  ");
                    } else {
                        printWriter.print(y + " ");
                    }
                    for (int x = 1; x <= boardSize; x++) {
                        Square sq = new Square(x, y);
                        for (String ship : placedShips.keySet()) {
                            if (placedShips.get(ship).contains(sq)) {
                                name = ship;
                                shipSquare = true;
                            }
                        }
                        printWriter.print("  ");
                        if (!shipSquare) {
                            //if it isn't a boat then it is the cannon or an empty square
                            printOceanBoardAdviser(printWriter, sq);
                        } else {
                            //it is a boat, so it prints the first letter of the boat's name
                            printWriter.print(Pin.fromName(name).getSymbol());
                            shipSquare = false;
                        }
                    }
                    printWriter.println();
                }
            }
        }
        printWriter.print("   ");
        for (int x = 1; x <= boardSize; x++) {
            //prints the x (column) numbers
            printOceanBoardHelp(printWriter, x);
        }
        printWriter.println();
        printWriter.println("Ships and their length:");
        printWriter.println("Carrier:5, Battleship:4, cRuiser:3, Submarine:3, Destroyer:2");
        printWriter.println("The Cannon is marked by an O");
        printWriter.println();

    }

    private void printOceanBoardHelp(PrintWriter printWriter, int x) {
        if (x < 10) {
            printWriter.print("  " + x);
        } else {
            printWriter.print(" " + x);
        }
    }

    private void printOceanBoardAdviser(PrintWriter printWriter, Square sq) {
        if (sq.equals(cannonSquare)) {
            printWriter.print("O");
        } else {
            printWriter.print(".");
        }
    }

    public void endCompetition(){
        synchronized(LOCK) {
            competitionOver = true;
            LOCK.notifyAll();
        }
    }

    public boolean isOver(){
        synchronized(LOCK) {
            try {
                LOCK.wait(WAIT_TIME);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        return competitionOver;
    }

    public boolean iWon() {
        return radar.iWon();
    }

    private class CompetitionService {
        public List<Square> invoke() {
            System.out.println("Incorrect direction");
            return Collections.emptyList();
        }
    }
}
