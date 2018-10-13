package airplan_1.edu.cyberapex.flightplanner.guide;

import airplan_1.edu.cyberapex.flightplanner.framework.Airline;
import airplan_1.edu.cyberapex.flightplanner.store.AirDatabase;
import airplan_1.edu.cyberapex.server.WebSessionService;
import airplan_1.edu.cyberapex.server.WebTemplate;
import airplan_1.edu.cyberapex.server.guide.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;

import java.util.HashMap;
import java.util.Map;

/**
 * Displays AirPlan tips.
 */
public class TipGuide extends AirGuide {
    protected static final String PATH = "/tips";
    protected static final String TITLE= "AirPlan Tips";

    private static final WebTemplate TIPS_TEMPLATE = new WebTemplate("TipsTemplate.html", TipGuide.class);


    public TipGuide(AirDatabase airDatabase, WebSessionService webSessionService) {
        super(airDatabase, webSessionService);
    }

    @Override
    public String getPath() {
        return PATH;
    }

    private String grabContents() {
        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("deleteMapURL", GuideUtils.generateDeleteMapURL());
        templateMap.put("summaryURL", GuideUtils.generateSummaryURL());

        return TIPS_TEMPLATE.getEngine().replaceTags(templateMap);
    }
    @Override
    protected HttpGuideResponse handlePull(HttpExchange exchange, String remainingPath, Airline airline) {
        return pullTemplateResponseWithoutMenuItems(TITLE, grabContents(), airline);
        }
}