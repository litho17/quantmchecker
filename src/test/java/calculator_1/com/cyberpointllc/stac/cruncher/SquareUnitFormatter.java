package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.FieldPosition;
import java.text.ParsePosition;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class SquareUnitFormatter extends CruncherFormatter {
    private static final GreatNumber NEGATIVE_ONE = new GreatNumber("-1");
    private static final GreatNumber SQUARE_SIXTEENTHS_PER_SQUARE_FOOT = new GreatNumber("36864");
    private static final GreatNumber SQUARE_SIXTEENTHS_PER_SQUARE_INCH = new GreatNumber("256");
    private static final String validCharacters = IntStream.range(0, 10).mapToObj(Integer::toString).collect(Collectors.joining()) + "'\"|";

    public SquareUnitFormatter() {
        super(validCharacters);
    }

    @Override
    public StringBuffer format(Object obj, StringBuffer toAppendTo, FieldPosition pos) {
        if (obj instanceof GreatNumber) {
            GreatNumber num = (GreatNumber)obj;

            if (num.isNegative()) {
                toAppendTo.append('-');
                num = num.multiply(NEGATIVE_ONE);
            }

            if (num.compareTo(SQUARE_SIXTEENTHS_PER_SQUARE_FOOT) >= 0) {
                GreatNumber feet = num.divide(SQUARE_SIXTEENTHS_PER_SQUARE_FOOT);
                num = num.subtract(feet.multiply(SQUARE_SIXTEENTHS_PER_SQUARE_FOOT));
                toAppendTo.append(feet);
                toAppendTo.append('\'');
            }

            if (num.compareTo(SQUARE_SIXTEENTHS_PER_SQUARE_INCH) >= 0) {
                GreatNumber inches = num.divide(SQUARE_SIXTEENTHS_PER_SQUARE_INCH);
                num = num.subtract(inches.multiply(SQUARE_SIXTEENTHS_PER_SQUARE_INCH));
                toAppendTo.append(inches);
                toAppendTo.append('\"');
            }

            toAppendTo.append(num);
            toAppendTo.append("|256");

            return toAppendTo;
        } else {
            throw new IllegalArgumentException("ConstructionFormatter can only format LargeInteger objects");
        }
    }

    @Override
    public Object parseObject(String source, ParsePosition pos) {
        String squareFeet = "0";
        String squareInches = "0";
        String squareSixteenths = "0";
        boolean negative = false;
        boolean end = false;
        source = source.trim();

        if (source.charAt(0) == '-') {
            negative = true;
            source = source.substring(1);
        }

        String[] split = source.split("\'");

        if (!end) {
            if (split.length == 1) {
                if (source.lastIndexOf("'") == (source.length() - 1)) {
                    squareFeet = split[0];
                    end = true;
                } else {
                    split = split[0].split("\"");
                }
            } else if (split.length == 2) {
                squareFeet = split[0];
                split = split[1].split("\"");
            } else {
                pos.setErrorIndex(0);
                return null;
            }
        }

        if (!end) {
            if (split.length == 1) {
                if (source.lastIndexOf("\"") == (source.length() - 1)) {
                    squareInches = split[0];
                    end = true;
                } else {
                    split = split[0].split("[|]");
                }
            } else if (split.length == 2) {
                squareInches = split[0];
                split = split[1].split("[|]");
            } else {
                pos.setErrorIndex(squareFeet.length() + 1);
                return null;
            }
        }

        if (!end) {
            if (split.length > 0 && split.length < 3) {
                squareSixteenths = split[0];
            } else {
                pos.setErrorIndex(squareFeet.length() + squareInches.length() + 2);
                return null;
            }
        }

        GreatNumber feetInSquareSixteenths = new GreatNumber(squareFeet);
        feetInSquareSixteenths = feetInSquareSixteenths.multiply(SQUARE_SIXTEENTHS_PER_SQUARE_FOOT);
        GreatNumber inchesInSquareSixteenths = new GreatNumber(squareInches);
        inchesInSquareSixteenths = inchesInSquareSixteenths.multiply(SQUARE_SIXTEENTHS_PER_SQUARE_INCH);
        GreatNumber totalSquareSixteenths = feetInSquareSixteenths.integrate(inchesInSquareSixteenths.integrate(new GreatNumber(squareSixteenths)));
        pos.setIndex((source.length()));

        return negative ? totalSquareSixteenths.multiply(NEGATIVE_ONE) : totalSquareSixteenths;
    }
}

