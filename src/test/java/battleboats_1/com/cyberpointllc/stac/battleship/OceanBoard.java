package battleboats_1.com.cyberpointllc.stac.battleship;

import plv.colorado.edu.quantmchecker.qual.Summary;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class OceanBoard {
    // allow a small amount of rounding error
    private static final double EPSILON = .0001;

    Competition competition;

    /**
     * oneSquaresLength is the length of one square in meters, this length is decided by the players.
     * The x and y of the square are both this length. These x and y are similar to OceanX and Y since
     * it accounts for the length.
     */
    private final double oneSquaresLength;

    /**
     * OceanSquareLength is the oneSquareLength/divisors in meters. Divisors is a number given by the player.
     * For example if the oneSquareLength is 1.0 and divisors is 4 then OceanSquareLength is .25
     * and the square is "divided" into 16ths.
     * It is used to determine where in the square the shot landed. This allows us to determine
     * if the shot is a vertex, line, or an internal hit.
     */
    private final double oceanSquareLength;

    /**
     * numberOfPixelsOnSide is the number squares in each row or col. This can be considered as the number
     * of pixels in each row and column. On the pixel level, the board is
     * numberOfPixelsOnSide x numberOfPixelsOnSide
     */
    private final int numberOfPixelsOnSide;

    //boats is the list of boats that are placed on the pixel level of the board
    private final List<Ship> ships;

    //cannon is the square where the cannon is located on the pixel level of the board
    private Square cannon;

    /**
     * @param size         - how many squares on the board in one direction (meaning its the length and width)
     * @param divisors     - number of columns and rows in one square
     * @param squareLength - full length of a square
     */
    public OceanBoard(int size, int divisors, double squareLength, Competition competition) {
        oneSquaresLength = squareLength;
        oceanSquareLength = squareLength / divisors;
        numberOfPixelsOnSide = size;

        this.competition = competition;
        ships = new ArrayList<>();
    }

    /**
     * @param ships          List of the player's placed ships
     * @param cannonCoordinates Square where the player placed the opponent's cannon
     * @throws IllegalStateException if there are no boats specified or the cannon location is <code>null</code>
     */
    @Summary({"this.ships", "ships"})
    public void fixShipsAndCannon(List<Ship> ships, Square cannonCoordinates) {
        if ((ships == null) || ships.isEmpty()) {
            throw new IllegalStateException("There must exist at least one boat");
        }

        if (cannonCoordinates == null) {
            throw new IllegalStateException("Cannon location may not be null");
        }

        this.ships.clear();
        this.ships.addAll(ships);

        cannon = cannonCoordinates;
    }

    /**
     * Indicates if the specified value is in the left/bottom margin.
     * This means the value is less than <code>oneSquaresLength/divisions</code>.
     * If the value is negative then the mod will make it positive to find its place in a square
     *
     * @param oceanVal remainder value of the hit
     * @return boolean true if the hit is in the first set of oceanSquareLength values
     */
    private boolean isInLeastOceanSquare(double oceanVal) {
        double wrap = oceanVal % oneSquaresLength;
        if (wrap < 0) {
            wrap += oneSquaresLength;
        }
        return (wrap < oceanSquareLength);
    }

    /**
     * Indicates if the specified value is in the top/right margin.
     * This means the value is greater than <code>oneSquaresLength - oneSquaresLength/divisions</code>.
     *
     * @param oceanVal value of the hit
     * @return boolean true if the hit is in the last set of oceanSquareLength values
     */
    private boolean isInGreatestOceanSquare(double oceanVal) {
        double wrap = oceanVal % oneSquaresLength;
        if (wrap < 0) {
            wrap += oneSquaresLength;
        }
        return (wrap > (oneSquaresLength - oceanSquareLength));
    }

    /**
     * Checks the boats to see if they're on the shot square.
     * This creates its peg from calling Boat's hit result
     * or, if no ship has that square, then making a Miss peg.
     *
     * @param strikes list to add the squares hit and their peg (hit or miss)
     * @param x    x value of the square hit
     * @param y    y value of the square hit
     * @return hits with the square and the resulting peg updated
     */

    private Map<Square, Pin> denoteStrikeSquare(Map<Square, Pin> strikes, int x, int y) {
        Square square = new Square(x, y);

        strikes.put(square, Pin.MISS);

        ships.forEach(ship -> {
            if (ship.contains(square)) {
                strikes.put(square, ship.strikeReport(square));
            }
        });

        return strikes;
    }

    /**
     * if xDistance or yDistance are greater than the board length
     * in any direction then the shot is off both boards.
     *
     * @param coordinate distance of the hit in the x or y direction (ocean coordinate)
     * @return boolean true if the hit is at least as long as the board
     */
    private boolean tooFar(BigDecimal coordinate) {
        // Add epsilon to allow for some rounding error
        BigDecimal boardLength = new BigDecimal(oneSquaresLength).multiply(new BigDecimal(numberOfPixelsOnSide));
        BigDecimal epsilon = new BigDecimal(EPSILON);
        boolean tooBig = coordinate.compareTo(boardLength.add(epsilon)) > 0;
        boolean tooSmall = coordinate.negate().compareTo(boardLength.add(epsilon)) > 0;
        return tooBig || tooSmall;

    }

    /**
     * @param pixelVal is x or y integer point value on the board (pixel coordinate)
     *                 (length of the squares is not considered here, it is simply the integer point value)
     * @return boolean true if it is on the radar board [-Size, Size]
     */
    private boolean onRadarBoard(int pixelVal) {
        return ((pixelVal <= numberOfPixelsOnSide) && (pixelVal >= -numberOfPixelsOnSide));
    }

    private boolean onOceanBoard(int pixelVal) {
        return ((pixelVal >= 0) && (pixelVal <= numberOfPixelsOnSide));
    }

    /**
     * @param strikes Map of the squares and pegs on the ocean board
     * @return Map of squares and pegs on the radar board
     */
    private Map<Square, Pin> oceanToRadar(Map<Square, Pin> strikes) {
        Map<Square, Pin> radarStrikes = new HashMap<>();

        strikes.forEach((sq, pin) -> {
            int pixelX = sq.fetchX() - cannon.fetchX();
            int pixelY = sq.obtainY() - cannon.obtainY();

            if ((pixelX == 0) && (pixelY == 0)) { // the cannon -- call it a miss
                radarStrikes.put(new Square(pixelX, pixelY), Pin.MISS);
            } else if (onRadarBoard(pixelX) && onRadarBoard(pixelY)) {
                radarStrikes.put(new Square(pixelX, pixelY), pin);
            }
        });

        return radarStrikes;
    }

    /**
     * Adding half of squareLength places the cannon directly in the
     * center of the square.  All pixel values are presumed positive.
     *
     * @param pixelVal the x or y point value for the square
     * @return double representing the mid point with respect to the length of a square
     */
    private double center(int pixelVal) {
        return (((double) pixelVal) * oneSquaresLength) + (0.5 * oneSquaresLength);
    }

    /**
     * Finds the hits from the Ocean board and returns them as a map of radar hits
     * to give to the other player.
     *
     * @param xGap distance in the x direction that the hit went from the cannon
     * @param yGap distance in the y direction that the hit went from the cannon
     * @return Map of the hit squares (on the radar board) and their peg
     */
    public Map<Square, Pin> getStrikeSquares(BigDecimal xGap, BigDecimal yGap) {
        Map<Square, Pin> strikes = grabOceanSquares(xGap, yGap);
        return oceanToRadar(strikes);
    }

    /**
     * @param xGap - the distance in the x direction that the hit went from the cannon
     * @param yGap - the distance in the y direction that the hit went from the cannon
     * @return Map of the hit squares (on the ocean board) and their peg
     */
    private Map<Square, Pin> grabOceanSquares(BigDecimal xGap, BigDecimal yGap) {
        Map<Square, Pin> strikes = new HashMap<>();

        // Ocean x and y are where on the board (square length
        // considered) that the shot will hit.  Note that x and y
        // distance are also in ocean values (meters).
        double oceanX = xGap.doubleValue() + center(cannon.fetchX());
        double oceanY = yGap.doubleValue() + center(cannon.obtainY());

        // Pixel x and y are the coordinates used to mark the boards;
        // they do not factor in the board with the size of the square.
        int pixelX = (int) Math.floor(oceanX / oneSquaresLength);
        int pixelY = (int) Math.floor(oceanY / oneSquaresLength);

        if (!onOceanBoard(pixelX) || !onOceanBoard(pixelY)) { // if true, we have shot beyond the oceanBoard (but we may still be on the radar board)
            if (tooFar(xGap) || tooFar(yGap)) { // if we're also off the radar board, that's not a secret
            // pixelX or pixelY distance from the cannon is larger than the board
                // so it's an automatic miss on both boards
                return new HashMap<>();
            }
        }

        strikes = fetchStrikes(strikes, xGap, yGap);

        // All hits have been found, now check if each square is sunk
        updateStrikesAsSunk(strikes);

        return strikes;
    }

    private Map<Square, Pin> fetchStrikes(Map<Square, Pin> strikes, BigDecimal xGap, BigDecimal yGap) {
        //Ocean x and y are where on the board (square length considered) that the
        //shot will hit. Note that x and y Distance are also ocean values.
        double oceanX = xGap.doubleValue() + center(cannon.fetchX());
        double oceanY = yGap.doubleValue() + center(cannon.obtainY());

        // Pixel x and y are the coordinates used to mark the boards;
        // they do not factor in the board with the size of the square.
        // Instead of computing pixelX and pixelY, try checking each square individually

        int highest = 2 * numberOfPixelsOnSide;
        int smallest = -2 * numberOfPixelsOnSide;
        List<Square> reports = IntStream.rangeClosed(smallest, highest)
                .mapToObj(x -> IntStream.rangeClosed(smallest, highest)
                        .mapToObj(y -> new Square(x, y)))
                .flatMap(ss -> ss.filter(s -> s.contains(oceanX, oceanY, oneSquaresLength)))
                .collect(Collectors.toList());
        if (reports.isEmpty()) {
            return strikes;
        }
        Square landing = reports.get(0);
        int pixelX = landing.fetchX();
        int pixelY = landing.obtainY();

        // Determine where in the square the oceanX or oceanY is
        // located based on its decimal (remainder) value.
        // If any of these are true then the hit will hit the square
        // in that specific direction (line hit).
        boolean one = isInLeastOceanSquare(oceanX);
        boolean secondary = isInGreatestOceanSquare(oceanX);
        boolean ground = isInLeastOceanSquare(oceanY);
        boolean top = isInGreatestOceanSquare(oceanY);

        // Always hits the square you land on. Then add any line hits.
        // Left and Right take care of vertex case.
        strikes = denoteStrikeSquare(strikes, pixelX, pixelY);

        if (top) {
            strikes = denoteStrikeSquare(strikes, pixelX, pixelY + 1);
        } else if (ground) {
            strikes = denoteStrikeSquare(strikes, pixelX, pixelY - 1);
        }

        if (one) {
            strikes = denoteStrikeSquare(strikes, pixelX - 1, pixelY);

            if (top) {
                strikes = denoteStrikeSquare(strikes, pixelX - 1, pixelY + 1);
            } else if (ground) {
                strikes = denoteStrikeSquare(strikes, pixelX - 1, pixelY - 1);
            }
        } else if (secondary) {
            strikes = denoteStrikeSquare(strikes, pixelX + 1, pixelY);

            if (top) {
                strikes = denoteStrikeSquare(strikes, pixelX + 1, pixelY + 1);
            } else if (ground) {
                strikes = denoteStrikeSquare(strikes, pixelX + 1, pixelY - 1);
            }
        }

        return strikes;
    }

    /**
     * check if the squares hit sunk the ship, if so change that squares peg value
     *
     * @param strikes map of the squares that were hit from a single shot
     */
    private void updateStrikesAsSunk(Map<Square, Pin> strikes) {
        Map<Square, Pin> strikesToUpdate = new HashMap<>();

        int highest = 2 * numberOfPixelsOnSide;
        int smallest = -2 * numberOfPixelsOnSide;
        IntStream.rangeClosed(smallest, highest)
                .mapToObj(x -> IntStream.rangeClosed(smallest, highest)
                        .mapToObj(y -> new Square(x, y)))
                .flatMap(ss -> ss.filter(strikes::containsKey))
                .forEach(sq -> ships.forEach(ship -> {
                    if (ship.contains(sq) && ship.isSunk()) {
                        strikesToUpdate.put(sq, Pin.fromName(ship.obtainName()));
                    }
                }));

        for (Square sq : strikesToUpdate.keySet()) {
            strikes.put(sq, strikesToUpdate.get(sq));
        }
    }

}
