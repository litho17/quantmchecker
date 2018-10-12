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

public class PanelFeetCruncherHandler extends AbstractCruncherHandler {
    public static final String WALK = "/construction/boardfeet";
    public static final String TITLE = "Construction Calculator: Board Feet";

    private static final String INSTRUCTIONS =
            "Board Feet is a unit of volume for timber. Enter your dimensions for height, width, and length below, then click submit.";

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngineCreator().fixText("<h5 style=\"display:inline-block\"><a href=\"/construction/riseandrun\">Rise & Run</a></h5>\n" +
            "<h5 style=\"display:inline-block\"><a href=\"/construction/circle\">Circle Operations</a></h5> <br>\n" +
            "{{previousResult}}<br><br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    Height: <input type=\"text\" name=\"heightFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"heightInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"heightSixteenths\" placeholder=\"/16\"/> /16 <br><br>\n" +
            "    Width: <input type=\"text\" name=\"widthFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"widthInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"widthSixteenths\" placeholder=\"/16\"/> /16 <br><br>\n" +
            "    Length: <input type=\"text\" name=\"lengthFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"lengthInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"lengthSixteenths\" placeholder=\"/16\"/> /16 <br><br>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>").composeTemplateEngine();

    private static final Set<String> FIELD_NAMES;
    static {
        FIELD_NAMES = new HashSet<>();
        FIELD_NAMES.add("heightFeet");
        FIELD_NAMES.add("heightInches");
        FIELD_NAMES.add("heightSixteenths");
        FIELD_NAMES.add("widthFeet");
        FIELD_NAMES.add("widthInches");
        FIELD_NAMES.add("widthSixteenths");
        FIELD_NAMES.add("lengthFeet");
        FIELD_NAMES.add("lengthInches");
        FIELD_NAMES.add("lengthSixteenths");
    }

    public PanelFeetCruncherHandler(NetSessionService netSessionService) {
        super(netSessionService, new Cruncher(new UnitFormatter()),
                new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(PanelFeetCruncherHandler.class).composeNetTemplate());
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
            String height = Utility.parseFields( MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "heightFeet", "heightInches", "heightSixteenths");
            String width = Utility.parseFields( MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "widthFeet", "widthInches", "widthSixteenths");
            String size = Utility.parseFields( MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES), "lengthFeet", "lengthInches", "lengthSixteenths");

            displayEquation = "Height: " + Utility.formatMeasurement(height, 1, false) + " Width: " + Utility.formatMeasurement(width, 1, false)
                    + " Length: " + Utility.formatMeasurement(size, 1, false);
            equation = "(" + height + " * " + width + " * " + size + ") / 144|16";
            report = takeCruncher().processEquation(equation, new VolumeUnitFormatter());
            report = Utility.formatMeasurement(report, 1, true);
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
