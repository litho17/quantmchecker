package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.FieldPosition;
import java.text.ParsePosition;

public class RomanNumeralFormatter extends CruncherFormatter {
    public RomanNumeralFormatter() {
        super("MDCLXVI0");
    }

    @Override
    public StringBuffer format(Object obj, StringBuffer toAppendTo, FieldPosition pos) {
        if (obj instanceof GreatNumber) {
            GreatNumber number = (GreatNumber)obj;
            int value = Integer.valueOf(number.toString());

            if (value > 3999 || value < -3999) {
                throw new ReportTooGreatDeviationCreator().assignMessage("Result cannot be greater than 3999 or less than -3999").composeReportTooGreatDeviation();
            } else {
                if (value == 0) {
                    toAppendTo.append(0);
                } else {
                    if (number.isNegative()) {
                        toAppendTo.append('-');
                        value *= -1;
                    }

                    while (value > 0) {
                        if (value >= 1000) {
                            toAppendTo.append('M');
                            value -= 1000;
                        } else if (value >= 900) {
                            toAppendTo.append("CM");
                            value -= 900;
                        } else if (value >= 500) {
                            toAppendTo.append('D');
                            value -= 500;
                        } else if (value >= 400) {
                            toAppendTo.append("CD");
                            value -= 400;
                        } else if (value >= 100) {
                            toAppendTo.append('C');
                            value -= 100;
                        } else if (value >= 90) {
                            toAppendTo.append("XC");
                            value -= 90;
                        } else if (value >= 50) {
                            toAppendTo.append('L');
                            value -= 50;
                        } else if (value >= 40) {
                            toAppendTo.append("XL");
                            value -= 40;
                        } else if (value >= 10) {
                            toAppendTo.append('X');
                            value -= 10;
                        } else if (value >= 9) {
                            toAppendTo.append("IX");
                            value -= 9;
                        } else if (value >= 5) {
                            toAppendTo.append('V');
                            value -= 5;
                        } else if (value >= 4) {
                            toAppendTo.append("IV");
                            value -= 4;
                        } else {
                            toAppendTo.append('I');
                            value -= 1;
                        }
                    }
                }

                return toAppendTo;
            }
        } else {
            throw new IllegalArgumentException("RomanNumeralFormatter can only format LargeInteger objects");
        }
    }

    @Override
    public Object parseObject(String source, ParsePosition pos) {
        int count = 0;
        int value = 0;
        int currIndex = pos.getIndex();
        String sign = "";
//        source = source.toUpperCase();
        char preChar = ' ';
        char nextChar;
        char currChar = source.charAt(currIndex);

        if (!source.equals("0")) {
            if (currChar == '-') {
                sign = "-";
                currIndex++;
            }

            while (currIndex < source.length()) {
                currChar = source.charAt(currIndex);
                currIndex++;

                if (preChar != currChar) {
                    count = 0;
                }

                if (currChar == 'M') {
                    value += 1000;
                } else if (currChar == 'D') {
                    value += 500;
                } else if (currChar == 'C') {
                    value += 100;

                    if (currIndex < source.length()) {
                        nextChar = source.charAt(currIndex);

                        if (nextChar == 'M' || nextChar == 'D') {
                            count++;

                            if (count > 3) {
                                pos.setErrorIndex(currIndex - 1);
                                return null;
                            }

                            if (nextChar == 'M') {
                                if (count < 2) {
                                    value += 800;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            } else {
                                if (count < 2) {
                                    value += 300;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            }

                            count = 0;
                        }
                    }
                } else if (currChar == 'L') {
                    value += 50;
                } else if (currChar == 'X') {
                    value += 10;

                    if (currIndex < source.length()) {
                        nextChar = source.charAt(currIndex);

                        if (nextChar == 'C' || nextChar == 'L') {
                            count++;

                            if (count > 3) {
                                pos.setErrorIndex(currIndex - 1);
                                return null;
                            }

                            if (nextChar == 'C') {
                                if (count < 2) {
                                    value += 80;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            } else {
                                if (count < 2) {
                                    value += 30;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            }

                            count = 0;
                        } else {
                            if (nextChar != 'X' && nextChar != 'V' && nextChar != 'I') {
                                pos.setErrorIndex(currIndex);
                                return null;
                            }
                        }
                    }
                } else if (currChar == 'V') {
                    value += 5;
                } else if (currChar == 'I') {
                    value += 1;

                    if (currIndex < source.length()) {
                        nextChar = source.charAt(currIndex);

                        if (nextChar == 'X' || nextChar == 'V') {
                            count++;

                            if (count > 3) {
                                pos.setErrorIndex(currIndex - 1);
                                return null;
                            }

                            if (nextChar == 'X') {
                                if (count < 2) {
                                    value += 8;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            } else {
                                if (count < 2) {
                                    value += 3;
                                    currIndex++;
                                } else {
                                    pos.setErrorIndex(currIndex);
                                    return null;
                                }
                            }

                            count = 0;
                        } else {
                            if (nextChar != 'I') {
                                pos.setErrorIndex(currIndex);
                                return null;
                            }
                        }
                    }
                } else {
                    pos.setErrorIndex(currIndex - 1);
                    return null;
                }

                count++;

                if (count > 3) {
                    return new RomanNumeralFormatterGuide(pos, currIndex).invoke();
                } else if ((currChar == 'D' && count > 1) || (currChar == 'L' && count > 1) || (currChar == 'V' && count > 1)) {
                    pos.setErrorIndex(currIndex - 1);
                    return null;
                } else {
                    preChar = currChar;
                }
            }
        }

        if (value > 3999) {
            pos.setErrorIndex(source.length());
            return null;
        }
        String str = sign + Integer.toString(value);
        pos.setIndex(currIndex);

        return new GreatNumber(str);
    }

    private class RomanNumeralFormatterGuide {
        private ParsePosition pos;
        private int currIndex;

        public RomanNumeralFormatterGuide(ParsePosition pos, int currIndex) {
            this.pos = pos;
            this.currIndex = currIndex;
        }

        public Object invoke() {
            pos.setErrorIndex(currIndex - 1);
            return null;
        }
    }
}
