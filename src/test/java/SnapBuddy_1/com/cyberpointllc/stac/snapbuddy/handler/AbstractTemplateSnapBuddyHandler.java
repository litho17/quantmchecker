package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebTemplate;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.Map;

public abstract class AbstractTemplateSnapBuddyHandler extends AbstractSnapBuddyHandler {

    private static final String TEMPLATE_RESOURCE = "template.html";

    public static final String SUPPRESS_TIMESTAMP = "suppressTimestamp";

    private WebTemplate template;

    protected AbstractTemplateSnapBuddyHandler(SnapService snapService) {
        super(snapService);
    }

    protected abstract String getTitle(SnapContext context);

    protected abstract String getContents(SnapContext context);

    protected String getTemplateResource() {
        return TEMPLATE_RESOURCE;
    }

    protected Map<String, String> getTemplateMap(SnapContext context) {
        assert (context != null) : "Context may not be null";
        @Bound("8") int i;
        @Inv("= map (+ c40 c41 c42 c43 c44 c45 c49 c50)") Map<String, String> map = new  HashMap();
        Person person = context.getActivePerson();
        c40: map.put("name", person.getName());
        c41: map.put("location", person.getLocation().getCity());
        c42: map.put("pid", getProfilePhotoIdentity(person));
        c43: map.put("profileURL", getProfilePhotoUrl(person));
        c44: map.put("title", getTitle(context));
        c45: map.put("contents", getContents(context));
        String suppressTimestamp = context.getUrlParam(SUPPRESS_TIMESTAMP);
        if (suppressTimestamp == null || suppressTimestamp.equalsIgnoreCase("false")) {
            // Assign these two fields AFTER calling getContents
            c49: map.put("timestamp", context.getDate().toString());
            c50: map.put("duration", String.valueOf(getDuration(context.getHttpExchange())));
        }
        return map;
    }

    private WebTemplate getTemplate() {
        if (template == null) {
            template = new  WebTemplate(getTemplateResource(), getClass());
        }
        return template;
    }

    protected HttpHandlerResponse process(SnapContext context) {
        String response = getTemplate().getEngine().replaceTags(getTemplateMap(context));
        return getResponse(response);
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        SnapContext snapContext = new  SnapContext(getPerson(httpExchange), httpExchange);
        return process(snapContext);
    }
}
