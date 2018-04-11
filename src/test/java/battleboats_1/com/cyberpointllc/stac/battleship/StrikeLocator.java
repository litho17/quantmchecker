package battleboats_1.com.cyberpointllc.stac.battleship;

import java.math.BigDecimal;
import java.math.MathContext;
import java.util.Map;

public class StrikeLocator {
    private static final int NUM_DIGITS = 10000;
    private static final MathContext mc = new MathContext(NUM_DIGITS);
    private static final BigDecimal G = new BigDecimal("9.8"); // m/sec^2
    private static final BigDecimal TWO = new BigDecimal("2");
    private static final BigDecimal A = new BigDecimal(-1).multiply(G, mc).divide(TWO, mc); // -G/2
    private static final BigDecimal SMALLEST_DELTA = new BigDecimal("1E-100"); // minimum required progress
    private static final BigDecimal EPSILON = new BigDecimal("1E-100"); // acceptable distance from desired value
    private static int ITERATIONS_TO_ALLOW = 25;

    private static final BigDecimal T_INIT = new BigDecimal(.001);

    private BigDecimal initHeight;
    private BigDecimal initSpeedX;
    private BigDecimal initSpeedY;
    private OceanBoard board;
    private double boardAngle;

    private final double hHighest = 15.0;
    private final double vHighest = 350.0;
    private final double zero = 0.0;
    private final double ninetyDegrees = (Math.PI / 2);

    private String errorMsg = null; // if this is non-null, their shot was invalid

    /**
     * @param board
     * @param initHeight
     * @param initVelocity
     * @param verticalAngle - in radians.   0 is straight ahead
     * @param boardAngle    - in radians.  0 is east
     */
    public StrikeLocator(OceanBoard board, String initHeightStr, String initSpeedStr, String verticalAngleStr, String boardAngleStr) {
        double verticalAngle;
        BigDecimal initSpeed;
        try {
            this.board = board;
            verticalAngle = Double.parseDouble(verticalAngleStr);
            boardAngle = Double.parseDouble(boardAngleStr);
            verticalAngle = toRadians(verticalAngle);
            this.boardAngle = toRadians(boardAngle);

            initSpeed = parse(initSpeedStr);
            this.initSpeedX = initSpeed.multiply(new BigDecimal(Math.cos(verticalAngle)));
            this.initSpeedY = initSpeed.multiply(new BigDecimal(Math.sin(verticalAngle)));
            this.initHeight = parse(initHeightStr);

            if (initHeight.compareTo(BigDecimal.ZERO) < 0 || initHeight.compareTo(new BigDecimal(hHighest)) > 0) {
                errorMsg = "height must be between 0 m and " + hHighest + " m";
            } else if (initSpeed.compareTo(BigDecimal.ZERO) <=0 || initSpeed.compareTo(new BigDecimal(vHighest)) > 0) {
                errorMsg = "velocity must be greater than 0 m/s and no greater than " + vHighest + " m/s";
            }
        } catch (Exception e){
            errorMsg = "Shot parameters could not be parsed";
        }

        }

    public Map<Square, Pin> calculateStrikeCoordinates() {
        BigDecimal timeTraveled = calculateStrikeTime();
        BigDecimal gap = pullGapTraveled(timeTraveled);
        BigDecimal xGap = gap.multiply(bigDec(Math.cos(boardAngle)), mc);
        BigDecimal yGap = gap.multiply(bigDec(Math.sin(boardAngle)), mc);

        Map<Square, Pin> strikeSquares = board.getStrikeSquares(xGap, yGap);
        return strikeSquares;
    }


    private BigDecimal pullGapTraveled(BigDecimal t) {
        return initSpeedX.multiply(t);
    }

    // helper to hopefully make code more readable
    private BigDecimal bigDec(double val) {
        return new BigDecimal(val);
    }

    public String pullErrorMessage() {
        return errorMsg;
    }

    public boolean assessErrorMessage() {
        return errorMsg != "";
    }

    private BigDecimal height(BigDecimal t) {
        BigDecimal report =
                A.multiply(t, mc).multiply(t, mc)
                        .add(initSpeedY.multiply(t, mc))
                        .add(initHeight);
        return report;
    }

    private BigDecimal verticalRate(BigDecimal t) {
        BigDecimal report =
                TWO.multiply(A, mc).multiply(t, mc)
                        .add(initSpeedY);
        return report;
    }

    // This is a step in Newton's method, where the function to find a root of is A*t^2 + v_y0*t + h_0 -- the equation for
    // the height of a projectile in motion
    private BigDecimal stride(BigDecimal t) {
	    BigDecimal verticalRate = verticalRate(t);
        if (verticalRate.compareTo(BigDecimal.ZERO) == 0){
	        verticalRate = EPSILON;
	    }
        BigDecimal report = t.subtract(height(t).divide(verticalRate, mc), mc);
        return report;
    }

    public double toRadians(double degree) {
        while (degree < 0.0) {
            degree += 360;
        }
        while (degree >= 360) {
            degree -= 360;
        }
        return (degree * (Math.PI / 180));
    }

    private BigDecimal calculateStrikeTime() {

        int iterations = 1;
        BigDecimal delta = null; // difference between consecutive t values
        BigDecimal previousDelta = null;
        int runOfDecreasingDeltas = 0;
        BigDecimal tPrevious;
        BigDecimal tCurrent = T_INIT;

        do {
            tPrevious = tCurrent;
            tCurrent = stride(tPrevious);

            
            // we look for long runs of increasingly smaller deltas to prevent slow iteration from running forever
            previousDelta = delta;
            delta = tPrevious.subtract(tCurrent).abs();
            if (previousDelta!=null && delta.compareTo(previousDelta) < 0){
                runOfDecreasingDeltas++;
            } else {
                runOfDecreasingDeltas = 0;
            }
            if (runOfDecreasingDeltas > ITERATIONS_TO_ALLOW){
                System.out.println("Breaking due to slow convergence");
                break;
            }
            iterations++;

        } while (tCurrent.subtract(tPrevious, mc).abs().compareTo(SMALLEST_DELTA) > 0 &&
                height(tCurrent).abs().compareTo(EPSILON) > 0);

        // if t <= 0 use other root (flip about point where slope is zero)
        tCurrent = validate(tCurrent);
        return tCurrent;
    }

    private BigDecimal validate(BigDecimal t){
        if (t.compareTo(BigDecimal.ZERO) < 0){
            BigDecimal tCenter = initSpeedY.negate().divide(TWO.multiply(A, mc), mc);
            t = tCenter.add(tCenter.subtract(t));
        }
        return t;
     }

    private BigDecimal parse(String val){
        return new BigDecimal(val);
    }

}
