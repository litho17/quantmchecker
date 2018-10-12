package calculator_1.com.cyberpointllc.stac.cruncher;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplateCreator;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.HttpHandlerResponse;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.MultipartAssistant;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngineCreator;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SimpleCruncherHandler extends AbstractCruncherHandler {

    public static final String WALK = "/calculator";
    public static final String TITLE = "Calculator";
    private static final String EQUATION_FIELD = "expression";

    private static final String INSTRUCTIONS =
            "Enter an integer expression below.  Valid operations are +, -, * or x, /, ^ (exponentiation), and r (nth root). " +
                    "You may also use parentheses.";

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngineCreator().fixText("{{previousResult}}<br><br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    Expression: <input type=\"text\" name=\"expression\" placeholder=\"Enter an expression\"/><br>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>").composeTemplateEngine();

    private static final Set<String> FIELD_NAMES = Collections.singleton(EQUATION_FIELD);

    public SimpleCruncherHandler(NetSessionService netSessionService) {
        super(netSessionService, new Cruncher(new GreatNumberFormatter()),
                new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(SimpleCruncherHandler.class).composeNetTemplate());
    }

    @Override
    public String grabWalk(){
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        String displayReport;
        String report = obtainUnknownMessage();
        String equation = grabEquationMessage();

        try {
            Map<String, List<String>> fields = MultipartAssistant.fetchMultipartValues(httpExchange, FIELD_NAMES);
            equation = Utility.parseField(fields, EQUATION_FIELD);

            report = takeCruncher().processEquation(equation);
        } catch (@InvUnk("Extend library class") InvalidEquationDeviation iee) {
            report = fetchInvalidEquationMessage();
        } catch (@InvUnk("Extend library class") ExpensiveFormulaDeviation eoe) {
            report = pullFailureMessage();
        } catch (@InvUnk("Extend library class") ReportTooGreatDeviation rtle) {
            report = pullFailureMessage();
        } catch (IllegalArgumentException iae) {
            report = pullFailureMessage();
        }

        displayReport = equation + " = " + report;
        return handleObtain(httpExchange, displayReport);
    }

    @Override
    protected TemplateEngine takeFormTemplate() {return FORM_TEMPLATE;}

    @Override
    protected String takeInstructions() {return INSTRUCTIONS;}

    @Override
    protected String pullTitle() {return TITLE;}
}
