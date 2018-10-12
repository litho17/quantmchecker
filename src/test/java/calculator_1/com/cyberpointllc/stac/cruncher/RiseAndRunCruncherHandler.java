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

public class RiseAndRunCruncherHandler extends AbstractCruncherHandler {
    public static final String WALK = "/construction/riseandrun";
    public static final String TITLE = "Construction Calculator: Rise and Run";

    private static final String INSTRUCTIONS =
            "Enter the rise and run dimensions below, then click submit.";

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngineCreator().fixText("<h5 style=\"display:inline-block\"><a href=\"/construction/boardfeet\">Board Feet</a></h5>\n" +
            "<h5 style=\"display:inline-block\"><a href=\"/construction/circle\">Circle Operations</a></h5> <br>\n" +
            "{{previousResult}}<br><br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    Rise: <input type=\"text\" name=\"riseFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"riseInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"riseSixteenths\" placeholder=\"/16\"/> /16 <br><br>\n" +
            "    Run: <input type=\"text\" name=\"runFeet\" placeholder=\"ft\"/> ft \n" +
            "    <input type=\"text\" name=\"runInches\" placeholder=\"in\"/> in \n" +
            "    <input type=\"text\" name=\"runSixteenths\" placeholder=\"/16\"/> /16 <br>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>").composeTemplateEngine();

    private static final Set<String> FIELD_NAMES;
    static {
        FIELD_NAMES = new HashSet<>();
        FIELD_NAMES.add("riseFeet");
        FIELD_NAMES.add("riseInches");
        FIELD_NAMES.add("riseSixteenths");
        FIELD_NAMES.add("runFeet");
        FIELD_NAMES.add("runInches");
        FIELD_NAMES.add("runSixteenths");
    }

    //Handler for the Rise and Run Calculator page
    public RiseAndRunCruncherHandler(NetSessionService netSessionService) {
        super(netSessionService, new Cruncher(new UnitFormatter()),
                new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(RiseAndRunCruncherHandler.class).composeNetTemplate());
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
            Map<String, List<String>> fields = MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES);
            String rise = Utility.parseFields(fields, "riseFeet", "riseInches", "riseSixteenths");
            String run = Utility.parseFields(fields, "runFeet", "runInches", "runSixteenths");

            displayEquation = "Rise: " + Utility.formatMeasurement(rise, 1, false) + " Run: " + Utility.formatMeasurement(run, 1, false);
            equation = "((" + rise + "^ 2|16) + (" + run + "^ 2|16))r 2|16";
            report = takeCruncher().processEquation(equation);
            report = Utility.formatMeasurement(report, 1, false);
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
