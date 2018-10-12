package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.FieldPosition;
import java.text.ParsePosition;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class GreatNumberFormatter extends CruncherFormatter {
    public GreatNumberFormatter() {
        super(IntStream.range(0, 100).mapToObj(Integer::toString).collect(Collectors.joining()));
        }

    @Override
    public StringBuffer format(Object obj, StringBuffer toAppendTo, FieldPosition pos) {
        if (obj instanceof GreatNumber) {
            GreatNumber number = (GreatNumber)obj;

            return new StringBuffer(number.toString());
        } else {
            throw new IllegalArgumentException("LargeIntegerFormatter can only format LargeInteger objects");
        }
    }

    @Override
    public Object parseObject(String source, ParsePosition pos) {
        GreatNumber value = null;

        try {
            value = new GreatNumber(source);
            pos.setIndex(source.length());
        } catch (NumberFormatException e) {
            pos.setErrorIndex(0);
        }

        return value;
    }
}