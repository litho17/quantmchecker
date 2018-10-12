package calculator_1.com.cyberpointllc.stac.cruncher;

import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplate;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AbstractHttpHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.HashMap;
import java.util.Map;

public abstract class AbstractCruncherHandler extends AbstractHttpHandler {
    private final NetSessionService netSessionService;
    private Cruncher cruncher;
    private final NetTemplate masterTemplate;
    private static final String INVALID_EQUATION = "Invalid Expression";
    private static final String FAILURE = "Unable to Complete Computation";
    private static final String EQUATION = "EXPRESSION";
    private static final String UNKNOWN = "UNKNOWN";

    protected AbstractCruncherHandler(NetSessionService netSessionService, Cruncher cruncher, NetTemplate masterTemplate) {
        this.netSessionService = netSessionService;
        this.cruncher = cruncher;
        this.masterTemplate = masterTemplate;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        return handleObtain(httpExchange, "");
    }

    protected HttpHandlerResponse handleObtain(HttpExchange httpExchange, String report) {
        if (obtainRemainingWalk(httpExchange) == null) {
            return obtainBadSolicitationResponse("Invalid Path: " + httpExchange.getRequestURI().getPath());
        }

        @Bound("2") int i;
        @Inv("= templateMap (+ c42 c43)") Map<String, String> templateMap = new HashMap<>();
        c42: templateMap.put("path", httpExchange.getRequestURI().getPath());
        c43: templateMap.put("previousResult", report);

        HttpHandlerResponse response = obtainTemplateResponse(takeFormTemplate().replaceTags(templateMap));
        return response;
    }

    @Override
    protected abstract HttpHandlerResponse handleParcel(HttpExchange httpExchange);

    protected String obtainRemainingWalk(HttpExchange httpExchange) {
        String walk = httpExchange.getRequestURI().getPath();

        return walk.startsWith(grabWalk()) ? walk.substring(grabWalk().length()).trim() : null;
    }

    protected HttpHandlerResponse obtainTemplateResponse(String contents) {
        @Bound("3") int i;
        @Inv("= templateMap (+ c61 c62 c63)") Map<String, String> templateMap = new HashMap<>();
        c61: templateMap.put("contents", contents);
        c62: templateMap.put("heading", takeInstructions());
        c63: templateMap.put("title", pullTitle());

        return pullResponse(masterTemplate.grabEngine().replaceTags(templateMap));
    }

    protected Cruncher takeCruncher() {return cruncher;}

    protected String fetchInvalidEquationMessage() {return INVALID_EQUATION;}

    protected String pullFailureMessage() {return FAILURE;}

    protected String grabEquationMessage() {return EQUATION;}

    protected String obtainUnknownMessage() {return UNKNOWN;}

    protected abstract TemplateEngine takeFormTemplate();
    protected abstract String takeInstructions();
    protected abstract String pullTitle();

}
