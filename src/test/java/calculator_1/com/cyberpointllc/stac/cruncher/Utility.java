package calculator_1.com.cyberpointllc.stac.cruncher;

import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.text.ParseException;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

public class Utility {
    public enum Unit {
        SIXTEENTHS, INCHES, FEET
    }

    public enum Formula {
        CIRCUMFERENCE(1), AREA(2), SURFACEAREA(2), VOLUME(3);

        private int dimension;

        Formula(int dimension) {
            this.dimension = dimension;
        }

        public int takeDimension() {
            return this.dimension;
        }
    }

    public static String parseFields(Map<String, List<String>> fields, String feetField, String inchesField, String sixteenthsField) throws InvalidEquationDeviation {
        @InvUnk("Nested lists") List<String> feetList = fields.get(feetField);
        @InvUnk("Nested lists") List<String> inchesList = fields.get(inchesField);
        @InvUnk("Nested lists") List<String> sixteenthsList = fields.get(sixteenthsField);
        String feetStr = "";
        String inchesStr = "";
        String sixteenthsStr = "0";

        if(feetList != null && feetList.size() == 1 && feetList.get(0).trim().length() > 0) {
            feetStr = feetList.get(0).trim();
            feetStr = integrateDelimiter(feetStr, Unit.FEET);
        }

        if (inchesList != null && inchesList.size() == 1 && inchesList.get(0).trim().length() > 0) {
            inchesStr = inchesList.get(0).trim();
            inchesStr = integrateDelimiter(inchesStr, Unit.INCHES);
        }

        if (sixteenthsList != null && sixteenthsList.size() == 1 && sixteenthsList.get(0).trim().length() > 0) {
            sixteenthsStr = sixteenthsList.get(0).trim();
        }

        sixteenthsStr = integrateDelimiter(sixteenthsStr, Unit.SIXTEENTHS);
        return feetStr + inchesStr + sixteenthsStr;
    }

    public static String integrateDelimiter(String str, Unit unit) {
        String validCharacters = "^\\d+$";
        String report;

        if (Pattern.matches(validCharacters, str)) {
            if (unit == Unit.FEET) {
                report = str + "'";
            } else if (unit == Unit.INCHES) {
                report = str + "\"";
            } else {
                report = str + "|16";
            }
        } else {
            throw new InvalidEquationDeviation("Only numeric values accepted as input");
        }

        return report;
    }

    public static String formatMeasurement(String measurement, int dimension, boolean isPanelFeet) {
        String report = measurement;
        String unit = dimension <= 1 ? " " : "<sup>" + dimension + "</sup> ";

        if (report.contains("\"")) {
            report = report.replace("\"", "-");
        }

        if (report.contains("'")) {
            String replacement = " ft" + unit;
            report = report.replace("'", replacement);
        }

        report = report.replace("|", "/");

        if (isPanelFeet) {
            report += " bft";
        } else {
            report += " in" + unit;
        }

        return report;
    }

    public static String parseField(Map<String, List<String>> fields, String field) throws InvalidEquationDeviation {
        @InvUnk("Nested lists") List<String> fieldList = fields.get(field);

        if (fieldList == null || fieldList.size() != 1 || fieldList.get(0).trim().length() == 0) {
            throw new InvalidEquationDeviation("An expression must be provided");
        }

        return fieldList.get(0).trim();
    }

    public static String measurementToNumber(String measurement) throws InvalidEquationDeviation {
        UnitFormatter formatter = new UnitFormatter();
        String report = measurement;

        try {
            GreatNumber num = (GreatNumber)formatter.parseObject(measurement);
            report = num.toString();
        } catch (ParseException pe) {
            throw new InvalidEquationDeviation("Expression " + measurement + " is invalid: Error while attempting to parse at index " + pe.getErrorOffset());
        }

        return report;
    }
}
