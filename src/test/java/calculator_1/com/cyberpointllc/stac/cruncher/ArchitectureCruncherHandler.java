package calculator_1.com.cyberpointllc.stac.cruncher;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplateCreator;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.HttpHandlerResponse;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.MultipartAssistant;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngineCreator;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ArchitectureCruncherHandler extends AbstractCruncherHandler {
    public static final String WALK = "/construction";
    public static final String TITLE = "Construction Calculator";

    private static final String INSTRUCTIONS =
            "Enter the dimensions and operation below. Valid operations are +, -, * or x, /" +
                    ", ^ (exponentiation), and r (nth root). ";

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngineCreator().fixText("<h5 style=\"display:inline-block\"><a href=\"/construction/riseandrun\">Rise & Run</a></h5>\n" +
            "<h5 style=\"display:inline-block\"><a href=\"/construction/boardfeet\">Board Feet</a></h5>\n" +
            "<h5 style=\"display:inline-block\"><a href=\"/construction/circle\">Circle Operations</a></h5> <br>\n" +
            "{{previousResult}}<br><br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    <input type=\"text\" name=\"leftFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"leftInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"leftSixteenths\" placeholder=\"/16\"/> /16 </br></br>\n" +
            "    <input type=\"text\" name=\"operator\" placeholder=\"op\" required/> operator </br></br>\n" +
            "    <input type=\"text\" name=\"rightFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"rightInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"rightSixteenths\" placeholder=\"/16\"/> /16 </br>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>").composeTemplateEngine();

    private static final Set<String> FIELD_NAMES;
    static {
        FIELD_NAMES = new HashSet<>();
        FIELD_NAMES.add("leftFeet");
        FIELD_NAMES.add("leftInches");
        FIELD_NAMES.add("leftSixteenths");
        FIELD_NAMES.add("operator");
        FIELD_NAMES.add("rightFeet");
        FIELD_NAMES.add("rightInches");
        FIELD_NAMES.add("rightSixteenths");
    }

    public ArchitectureCruncherHandler(NetSessionService netSessionService) {
        super(netSessionService, new Cruncher(new UnitFormatter()),
                new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(ArchitectureCruncherHandler.class).composeNetTemplate());
    }

    @Override
    public String grabWalk(){
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        String displayReport;
        String report = obtainUnknownMessage();
        String displayEquation = grabEquationMessage();
        String zeroValues = "0|16 0'0|16 0\"0|16 0'0\"0|16";

        try {
            String procedure = Utility.parseField(MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "operator");
            String firstOperand = Utility.parseFields(MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "leftFeet", "leftInches", "leftSixteenths");
            String secondaryOperand = Utility.parseFields(MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "rightFeet", "rightInches", "rightSixteenths");
            String equation = firstOperand + procedure + secondaryOperand;
            displayEquation = Utility.formatMeasurement(firstOperand, 0, false) + " " + procedure + " " + Utility.formatMeasurement(secondaryOperand, 0, false);
            int dimension = 1;
            boolean toNumber = false;

            if (procedure.equals("*") || procedure.equals("x")) {
                report = takeCruncher().processEquation(equation, new SquareUnitFormatter());
                dimension = 2;
            } else {
                report = takeCruncher().processEquation(equation);

                if (procedure.equals("/") || (procedure.equals("^") && zeroValues.contains(secondaryOperand))) {
                    toNumber = true;
                }
            }

            if (toNumber) {
                report = Utility.measurementToNumber(report);
            } else {
                report = Utility.formatMeasurement(report, dimension, false);
            }
        } catch (@InvUnk("Extend library class") InvalidEquationDeviation iee) {
            report = fetchInvalidEquationMessage();
        } catch (@InvUnk("Extend library class") ExpensiveFormulaDeviation eoe) {
            report = pullFailureMessage();
        } catch (@InvUnk("Extend library class") ReportTooGreatDeviation rtle) {
            report = pullFailureMessage();
        } catch (IllegalArgumentException iae) {
            report = pullFailureMessage();
        }

        displayReport = displayEquation + " = " + report;
        return handleObtain(httpExchange, displayReport);
    }

    @Override
    protected TemplateEngine takeFormTemplate() {return FORM_TEMPLATE;}

    @Override
    protected String takeInstructions() {return INSTRUCTIONS;}

    @Override
    protected String pullTitle() {return TITLE;}
}
