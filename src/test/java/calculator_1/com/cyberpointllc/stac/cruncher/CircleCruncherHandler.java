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

public class CircleCruncherHandler extends AbstractCruncherHandler {
    public static final String WALK = "/construction/circle";
    public static final String TITLE = "Construction Calculator: Circle Calculator";

    private static final String INSTRUCTIONS =
            "Enter the dimensions for the radius and select an operation below, then click submit.";

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngineCreator().fixText("<h5 style=\"display:inline-block\"><a href=\"/construction/riseandrun\">Rise & Run</a></h5>\n" +
            "<h5 style=\"display:inline-block\"><a href=\"/construction/boardfeet\">Board Feet</a></h5> <br>\n" +
            "{{previousResult}}<br><br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    Radius: <input type=\"text\" name=\"feet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"inches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"sixteenths\" placeholder=\"/16\"/> /16 <br><br>\n" +
            "    Operation: <input type=\"radio\" name=\"operation\" value=\"Area\" checked/> Area \n" +
            "    <input type=\"radio\" name=\"operation\" value=\"Circumference\"/> Circumference \n" +
            "    <input type=\"radio\" name=\"operation\" value=\"SurfaceArea\"/> Surface Area (Sphere)\n" +
            "    <input type=\"radio\" name=\"operation\" value=\"Volume\"/> Volume (Sphere)<br>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>").composeTemplateEngine();

    private static final Set<String> FIELD_NAMES;
    static {
        FIELD_NAMES = new HashSet<>();
        FIELD_NAMES.add("feet");
        FIELD_NAMES.add("inches");
        FIELD_NAMES.add("sixteenths");
        FIELD_NAMES.add("operation");
    }

    private static final String PI = "355|16 / 113|16";

    //Handler for the Circle Calculator page
    public CircleCruncherHandler(NetSessionService netSessionService) {
        super(netSessionService, new Cruncher(new UnitFormatter()),
                new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(CircleCruncherHandler.class).composeNetTemplate());
    }

    @Override
    public String grabWalk(){
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        String displayReport;
        String equation;
        String report = obtainUnknownMessage();
        String displayEquation = grabEquationMessage();

        try {
            String radius = Utility.parseFields(MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "feet", "inches", "sixteenths");
            String inputFormula = Utility.parseField(MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "operation");
            Utility.Formula formula;
            displayEquation = "Operation: " + inputFormula + " Radius: " + Utility.formatMeasurement(radius, 1, false);

            if (inputFormula.equals("Area")) {
                equation = "(" + radius + "^2|16) * " + PI;
                report = takeCruncher().processEquation(equation, new SquareUnitFormatter());
                formula = Utility.Formula.AREA;
            } else if (inputFormula.equals("Circumference")) {
                equation = "2|16 * " + radius + " * " + PI;
                report = takeCruncher().processEquation(equation);
                formula = Utility.Formula.CIRCUMFERENCE;
            } else if (inputFormula.equals("Surface Area")) {
                equation = "4|16 * (" + radius + "^2|16) * " + PI;
                report = takeCruncher().processEquation(equation, new SquareUnitFormatter());
                formula = Utility.Formula.SURFACEAREA;
            } else if (inputFormula.equals("Volume")) {
                equation = "4|16 * (" + radius + "^3|16) * " + PI + " / 3|16";
                report = takeCruncher().processEquation(equation, new VolumeUnitFormatter());
                formula = Utility.Formula.VOLUME;
            } else {
                throw new IllegalArgumentException("Only Area, Circumference, Surface Area, and Volume are valid operations");
            }

            report = Utility.formatMeasurement(report, formula.takeDimension(), false);
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