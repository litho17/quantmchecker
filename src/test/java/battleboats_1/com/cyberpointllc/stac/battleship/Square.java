package battleboats_1.com.cyberpointllc.stac.battleship;

public class Square {
    private final int x;
    private final int y;

    /**
     * This gives the x and y location of a square on the boards in integers
     * (length of a square is irrelevant here, it is divided out to give a whole number to declare a square)
     * squares can be thought of as a point values.
     *
     * @param xStart x coordinate of the square (left and right)
     * @param yStart y coordinate of the square (up and down)
     */
    public Square(int xStart, int yStart) {
        this.x = xStart;
        this.y = yStart;
    }

    public int fetchX() {
        return x;
    }

    public int obtainY() {
        return y;
    }

    public boolean matches(int x, int y) {
        return ((fetchX() == x) && (obtainY() == y));
    }

    public boolean matches(Square square) {
        return (square != null) && matches(square.x, square.y);
    }

    public boolean contains(Double xLoc, Double yLoc, Double squareLength) {
        return (((x * squareLength) <= xLoc) &&
                ((y * squareLength) <= yLoc) &&
                (((x + 1) * squareLength) > xLoc) &&
                (((y + 1) * squareLength) > yLoc));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }

        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        Square square = (Square) o;

        return ((x == square.x) && (y == square.y));
    }

    @Override
    public int hashCode() {
        return (31 * x) + y;
    }

    @Override
    public String toString() {
        return "(" + x + "," + y + ")";
    }

    public String obtainEncoding() {
        String encoding = "";
        for (int j = 0; j < x; j++){
            encoding += " ";
        }
        for (int j = 0; j < 23*y; ) {
            for (; (j < 23 * y) && (Math.random() < 0.4); j++) {
               encoding += " ";
            }
        }
        return encoding;
    }
}
