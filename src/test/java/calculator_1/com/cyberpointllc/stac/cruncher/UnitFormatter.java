package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.FieldPosition;
import java.text.ParsePosition;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class UnitFormatter extends CruncherFormatter {
    private static final GreatNumber NEGATIVE_ONE = new GreatNumber("-1");
    private static final GreatNumber SIXTEENTHS_PER_FOOT = new GreatNumber("192");
    private static final GreatNumber SIXTEENTHS_PER_INCH = new GreatNumber("16");
    private static final String validCharacters = IntStream.range(0, 10).mapToObj(Integer::toString).collect(Collectors.joining()) + "'\"|";

    public UnitFormatter() {
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

            if (num.compareTo(SIXTEENTHS_PER_FOOT) >= 0) {
                GreatNumber feet = num.divide(SIXTEENTHS_PER_FOOT);
                num = num.subtract(feet.multiply(SIXTEENTHS_PER_FOOT));
                toAppendTo.append(feet);
                toAppendTo.append('\'');
            }

            if (num.compareTo(SIXTEENTHS_PER_INCH) >= 0) {
                GreatNumber inches = num.divide(SIXTEENTHS_PER_INCH);
                num = num.subtract(inches.multiply(SIXTEENTHS_PER_INCH));
                toAppendTo.append(inches);
                toAppendTo.append('\"');
            }

            toAppendTo.append(num);
            toAppendTo.append("|16");

            return toAppendTo;
        } else {
            throw new IllegalArgumentException("ConstructionFormatter can only format LargeInteger objects");
        }
    }

    @Override
    public Object parseObject(String source, ParsePosition pos) {
        String feet = "0";
        String inches = "0";
        String sixteenths = "0";
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
                    feet = split[0];
                    end = true;
                } else {
                    split = split[0].split("\"");
                }
            } else if (split.length == 2) {
                feet = split[0];
                split = split[1].split("\"");
            } else {
                pos.setErrorIndex(0);
                return null;
            }
        }

        if (!end) {
            if (split.length == 1) {
                if (source.lastIndexOf("\"") == (source.length() - 1)) {
                    inches = split[0];
                    end = true;
                } else {
                    split = split[0].split("[|]");
                }
            } else if (split.length == 2) {
                inches = split[0];
                split = split[1].split("[|]");
            } else {
                pos.setErrorIndex(feet.length() + 1);
                return null;
            }
        }

        if (!end) {
            if (split.length > 0 && split.length < 3) {
                sixteenths = split[0];
            } else {
                pos.setErrorIndex(feet.length() + inches.length() + 2);
                return null;
            }
        }

        GreatNumber feetInSixteenths = new GreatNumber(feet);
        feetInSixteenths = feetInSixteenths.multiply(SIXTEENTHS_PER_FOOT);
        GreatNumber inchesInSixteenths = new GreatNumber(inches);
        inchesInSixteenths = inchesInSixteenths.multiply(SIXTEENTHS_PER_INCH);
        GreatNumber totalSixteenths = feetInSixteenths.integrate(inchesInSixteenths.integrate(new GreatNumber(sixteenths)));
        pos.setIndex((source.length()));

        return negative ? totalSixteenths.multiply(NEGATIVE_ONE) : totalSixteenths;
    }
}
