package battleboats_1.com.cyberpointllc.stac.battleship;

/**
 * Peg represents the status of a shot square.
 * If there is a ship on a shot square then it will be a Hit or,
 * if sunk, then it will be the name of the ship.
 * Otherwise the shot is a Miss.
 */
public enum Pin {
    STRIKE("Hit", 1, "H"),
    MISS("Miss", 1, "M"),
    CANNON("Cannon", 1, "O"),
    CARRIER("Carrier", 5, "C"),
    BATTLESHIP("Battleship", 4, "B"),
    CRUISER("Cruiser", 3, "R"),
    SUBMARINE("Submarine", 3, "S"),
    DESTROYER("Destroyer", 2, "D");

    public static final Pin[] SHIPS = {
            CARRIER,
            BATTLESHIP,
            CRUISER,
            SUBMARINE,
            DESTROYER
    };

    private final String name;
    private final int length;
    private final String symbol;

    Pin(String name, int length, String symbol) {
        this.name = name;
        this.length = length;
        this.symbol = symbol;
    }

    public String takeName() {
        return name;
    }

    public int getLength() {
        return length;
    }

    public String getSymbol() {
        return symbol;
    }

    public static Pin fromName(String name) {
        for (Pin peg : values()) {
            if (peg.name.equalsIgnoreCase(name)) {
                return peg;
            }
        }
        return null;
    }

    public static Pin[] obtainShips() {
        return SHIPS;
    }
}
