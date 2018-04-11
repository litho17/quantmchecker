package battleboats_1.com.cyberpointllc.stac.battleship;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class RadarBoard {
    private final int length;
    private final int numberOfShips;

    private final Set<Pin> sunkShips;
    private final Square cannon;
    public final Map<Square, Pin> board;

    /**
     * This board is for the player to see where their shots hit in
     * relation to the cannon at (0,0) since its real placement is
     * unknown to the player shooting.
     *
     * @param length length and width of the board (4 times larger than the Ocean Board)
     */
    public RadarBoard(int length, int numberOfShips) {
        if (length <= 0) {
            throw new IllegalArgumentException("Radar board size must be positive: " + length);
        }

        if (numberOfShips < 0) {
            throw new IllegalArgumentException("Number of boats may not be negative: " + numberOfShips);
        }

        this.length = length;
        this.numberOfShips = numberOfShips;

        sunkShips = new HashSet<>();
        cannon = new Square(0, 0);

        board = new HashMap<>();
        board.put(cannon, Pin.CANNON);
    }

    /**
     * Updates the radar board with the specified pegs
     * on the squares as a result of our shot.
     * Note: all squares should be on the RadarBoard
     *
     * @param strikeSquares Map from oceanBoard's getHitSquares so the player can peg the
     *                   squares that got hit as a result of its shot
     */
    public void layPins(Map<Square, Pin> strikeSquares) {
        if (strikeSquares != null) {
            layPinsManager(strikeSquares);
        }
    }

    private void layPinsManager(Map<Square, Pin> strikeSquares) {
        strikeSquares.forEach((square, pin) -> {
            if (!cannon.matches(square)) {
                layPinsManagerHome(square, pin);
            }
        });
    }

    private void layPinsManagerHome(Square square, Pin pin) {
        board.put(square, pin);

        if ((pin != Pin.CANNON) && (pin != Pin.STRIKE) && (pin != Pin.MISS)) {
            // If it is a ship name then add it to the list of
            // sunk ships so we can tell how many are sunk
            sunkShips.add(pin);
        }
    }

    /**
     * Returns an indication if the game has been won.
     * Since sunkShips contains the boats sunk in the
     * method placePegs, then it is used to determine
     * if this player has sunk them all.
     *
     * @return boolean true if all ships have been sunk
     * @see #layPins(Map)
     */
    public boolean iWon() {
        return sunkShips.size() == numberOfShips;
    }
}
