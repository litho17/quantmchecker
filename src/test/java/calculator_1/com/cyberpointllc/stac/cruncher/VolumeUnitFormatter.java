package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.FieldPosition;
import java.text.ParsePosition;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class VolumeUnitFormatter extends CruncherFormatter {
    private static final GreatNumber NEGATIVE_ONE = new GreatNumber("-1");
    private static final GreatNumber SIXTEENTHS_PER_FOOT = new GreatNumber("192");
    private static final GreatNumber SIXTEENTHS_PER_INCH = new GreatNumber("16");
    private static final GreatNumber VOLUME_SIXTEENTHS_PER_VOLUME_FOOT = new GreatNumber("7077888");
    private static final GreatNumber VOLUME_SIXTEENTHS_PER_VOLUME_INCH = new GreatNumber("4096");
    private static final String validCharacters = IntStream.range(0, 10).mapToObj(Integer::toString).collect(Collectors.joining()) + "'\"|";

    public VolumeUnitFormatter() {
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

            if (num.compareTo(VOLUME_SIXTEENTHS_PER_VOLUME_FOOT) >= 0) {
                GreatNumber feet = num.divide(VOLUME_SIXTEENTHS_PER_VOLUME_FOOT);
                num = num.subtract(feet.multiply(VOLUME_SIXTEENTHS_PER_VOLUME_FOOT));
                toAppendTo.append(feet);
                toAppendTo.append('\'');
            }

            if (num.compareTo(VOLUME_SIXTEENTHS_PER_VOLUME_INCH) >= 0) {
                GreatNumber inches = num.divide(VOLUME_SIXTEENTHS_PER_VOLUME_INCH);
                num = num.subtract(inches.multiply(VOLUME_SIXTEENTHS_PER_VOLUME_INCH));
                toAppendTo.append(inches);
                toAppendTo.append('\"');
            }

            toAppendTo.append(num);
            toAppendTo.append("|4096");

            return toAppendTo;
        } else {
            throw new IllegalArgumentException("ConstructionFormatter can only format LargeInteger objects");
        }
    }

    @Override
    public Object parseObject(String source, ParsePosition pos) {
        String volumeFeet = "0";
        String volumeInches = "0";
        String volumeSixteenths = "0";
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
                    volumeFeet = split[0];
                    end = true;
                } else {
                    split = split[0].split("\"");
                }
            } else if (split.length == 2) {
                volumeFeet = split[0];
                split = split[1].split("\"");
            } else {
                pos.setErrorIndex(0);
                return null;
            }
        }

        if (!end) {
            if (split.length == 1) {
                if (source.lastIndexOf("\"") == (source.length() - 1)) {
                    volumeInches = split[0];
                    end = true;
                } else {
                    split = split[0].split("[|]");
                }
            } else if (split.length == 2) {
                volumeInches = split[0];
                split = split[1].split("[|]");
            } else {
                pos.setErrorIndex(volumeFeet.length() + 1);
                return null;
            }
        }

        if (!end) {
            if (split.length > 0 && split.length < 3) {
                volumeSixteenths = split[0];
            } else {
                pos.setErrorIndex(volumeFeet.length() + volumeInches.length() + 2);
                return null;
            }
        }

        GreatNumber feetInVolumeSixteenths = new GreatNumber(volumeFeet);
        feetInVolumeSixteenths = feetInVolumeSixteenths.multiply(VOLUME_SIXTEENTHS_PER_VOLUME_FOOT);
        GreatNumber inchesInVolumeSixteenths = new GreatNumber(volumeInches);
        inchesInVolumeSixteenths = inchesInVolumeSixteenths.multiply(VOLUME_SIXTEENTHS_PER_VOLUME_INCH);
        GreatNumber totalVolumeSixteenths = feetInVolumeSixteenths.integrate(inchesInVolumeSixteenths.integrate(new GreatNumber(volumeSixteenths)));
        pos.setIndex((source.length()));

        return negative ? totalVolumeSixteenths.multiply(NEGATIVE_ONE) : totalVolumeSixteenths;
    }
}
