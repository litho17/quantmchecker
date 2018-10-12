package calculator_1.com.cyberpointllc.stac.cruncher;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplateCreator;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplate;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AbstractHttpHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.HashMap;
import java.util.Map;

public class HomePageHandler extends AbstractHttpHandler {

    public static final String WALK = "/home";
    public static final String TITLE = "Calculator Suite";

    private static final String INSTRUCTIONS =
            "Choose which calculator you would like to use from the selection above.";

    private final NetSessionService netSessionService;
    private Cruncher cruncher;
    private final NetTemplate masterTemplate;

    public HomePageHandler(NetSessionService netSessionService) {
        this.netSessionService = netSessionService;
        this.cruncher = new Cruncher(new GreatNumberFormatter());
        this.masterTemplate = new NetTemplateCreator().defineResourceName("homepagetemplate.html").assignLoader(HomePageHandler.class).composeNetTemplate();
    }

    @Override
    public String grabWalk(){
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        return handleTake(httpExchange, "");
    }

    protected HttpHandlerResponse handleTake(HttpExchange httpExchange, String report) {
        if (fetchRemainingWalk(httpExchange) == null) {
            return obtainBadSolicitationResponse("Invalid Path: " + httpExchange.getRequestURI().getPath());
        }
        @Bound("2") int i;
        @Inv("= templateMap (+ c49 c50)") Map<String, String> templateMap = new HashMap<>();
        c49: templateMap.put("path", httpExchange.getRequestURI().getPath());
        c50: templateMap.put("previousResult", report);

        HttpHandlerResponse response = grabTemplateResponse();
        return response;
    }

    protected String fetchRemainingWalk(HttpExchange httpExchange) {
        String walk = httpExchange.getRequestURI().getPath();

        return walk.startsWith(grabWalk()) ? walk.substring(grabWalk().length()).trim() : null;
    }

    protected HttpHandlerResponse grabTemplateResponse() {
        @Bound("2") int i;
        @Inv("= templateMap (+ c65 c66)") Map<String, String> templateMap = new HashMap<>();
        c65: templateMap.put("heading", INSTRUCTIONS);
        c66: templateMap.put("title", TITLE);

        return pullResponse(masterTemplate.grabEngine().replaceTags(templateMap));
    }
}
