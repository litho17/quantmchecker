package battleboats_1.com.cyberpointllc.stac.battleship;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Ship {
    private final String name;
    private final Map<Square, Boolean> shipCoordinates;

    public Ship(String name, List<Square> shipSquares) {
        if ((name == null) || name.trim().isEmpty()) {
            throw new IllegalArgumentException("Boat name may not be null or empty");
        }

        if ((shipSquares == null) || shipSquares.isEmpty()) {
            throw new IllegalArgumentException("Boat squares must exist");
        }

        this.name = name.trim();
        this.shipCoordinates = new HashMap<>();

        // Initialize each ship square as un-hit
        shipSquares.forEach(square -> this.shipCoordinates.put(square, false));
    }

    public String obtainName() {
        return name;
    }

    public boolean contains(Square square) {
        return shipCoordinates.containsKey(square);
    }

    /**
     * Determines if the shot hits a square that a Boat resides on.
     * If there is a boat there then the shotResult is a Hit and
     * this value in boat's map entry is updated.  This will
     * help determine if the ship has been sunk.
     *
     * @param strikeSquare square that was hit from ocean board
     * @return Peg indicating if a hit or miss
     */
    public Pin strikeReport(Square strikeSquare) {
        if (shipCoordinates.containsKey(strikeSquare)) {
            return new ShipFunction(strikeSquare).invoke();
        }

        return Pin.MISS;
    }

    /**
     * Indicates if the ship is considered sunk.
     * A ship is sunk if every square's value for that Boat is true.
     *
     * @return boolean true if the ship is considered sunk
     */
    public boolean isSunk() {
        for (Boolean strike : shipCoordinates.values()) {
            if (!strike) {
                return false;
            }
        }

        return true;
    }

    private class ShipFunction {
        private Square strikeSquare;

        public ShipFunction(Square strikeSquare) {
            this.strikeSquare = strikeSquare;
        }

        public Pin invoke() {
            shipCoordinates.put(strikeSquare, true);
            return Pin.STRIKE;
        }
    }
}
