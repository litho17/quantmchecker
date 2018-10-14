package SnapBuddy_1.com.cyberpointllc.stac.webserver.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebTemplate;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.util.Arrays;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class AuthenticationHandler extends AbstractHttpHandler {

    private final String redirectResponsePath;

    private final WebTemplate template;

    private static final String PATH = "/authenticate";

    private static final String TITLE = "Authenticate Server";

    private static final String KEY_FIELD = "A";

    private static final String TIMESTAMP_FIELD = "setTimestamp";

    private static final TemplateEngine TEMPLATE_ENGINE = new  TemplateEngine("<center>" + "<form action=\"" + PATH + "\" method=\"post\" enctype=\"multipart/form-data\"/>" + "    <textarea name=\"" + KEY_FIELD + "\" placeholder=\"Enter your public key\"" + "       rows=\"10\" cols=\"100\"/></textarea><br/>" + "    <input type=\"submit\" value=\"Compute the master secret\" name=\"submit\" />" + "    <input type=\"hidden\" name=\"" + TIMESTAMP_FIELD + "\" value=\"{{includeTimestamp}}\">" + "</form>" + "</center>");

    public AuthenticationHandler(String redirectResponsePath) {
        this.redirectResponsePath = redirectResponsePath;
        this.template = new  WebTemplate("basiccontenttemplate.html", getClass());
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        @Bound("5") int i;
        @Inv("= contentsTemplateMap (+ c48 c52)") Map<String, String> contentsTemplateMap = new  HashMap();
        @Inv("= templateMap (+ c49 c50 c54 c55)") Map<String, String> templateMap = new  HashMap();
        String suppressTimestamp = getUrlParam(httpExchange, "suppressTimestamp");
        if (suppressTimestamp == null || !suppressTimestamp.equals("true")) {
            c48: contentsTemplateMap.put("includeTimestamp", "true");
            c49: templateMap.put("timestamp", (new  Date()).toString());
            c50: templateMap.put("duration", String.valueOf(getDuration(httpExchange)));
        } else {
            c52: contentsTemplateMap.put("includeTimestamp", "false");
        }
        c54: templateMap.put("contents", TEMPLATE_ENGINE.replaceTags(contentsTemplateMap));
        c55: templateMap.put("title", TITLE);
        return getResponse(template.getEngine().replaceTags(templateMap));
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        @Inv("= fieldNames (+ c65 c66)") Set<String> fieldNames = new  HashSet();
        c65: fieldNames.add(KEY_FIELD);
        c66: fieldNames.add(TIMESTAMP_FIELD);
        @InvUnk("Nested lists") Map<String, List<String>> fieldNameItems = MultipartHelper.getMultipartValues(httpExchange, fieldNames);
        String usersPublicKey = "";
        boolean includeTimestamp = true;
        int conditionObj0 = 1;
        if (fieldNameItems.get(KEY_FIELD) != null && fieldNameItems.get(KEY_FIELD).size() == conditionObj0) {
            usersPublicKey = fieldNameItems.get(KEY_FIELD).get(0);
        }
        int conditionObj1 = 1;
        if (fieldNameItems.get(TIMESTAMP_FIELD) != null && fieldNameItems.get(TIMESTAMP_FIELD).size() == conditionObj1) {
            String timestamp = fieldNameItems.get(TIMESTAMP_FIELD).get(0);
            if (timestamp.equals("false")) {
                includeTimestamp = false;
            }
        }
        String urlEnd = "";
        if (usersPublicKey != null) {
            urlEnd = usersPublicKey;
        }
        String suppressTimestamp = getUrlParam(httpExchange, "suppressTimestamp");
        if (!includeTimestamp || (suppressTimestamp != null && suppressTimestamp.equals("true"))) {
            urlEnd += "?suppressTimestamp=true";
        }
        return getRedirectResponse(redirectResponsePath + "/" + urlEnd);
    }
}
