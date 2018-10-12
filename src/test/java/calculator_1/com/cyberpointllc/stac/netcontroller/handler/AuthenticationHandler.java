package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplateCreator;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplate;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngineCreator;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class AuthenticationHandler extends AbstractHttpHandler {
    private final String redirectResponseWalk;
    private final NetTemplate template;
    private static final String WALK = "/authenticate";
    private static final String TITLE = "Authenticate Server";
    private static final String CODE_FIELD = "A";
    private static final String TIMESTAMP_FIELD = "setTimestamp";
    private static final TemplateEngine TEMPLATE_ENGINE = new TemplateEngineCreator().fixText("<center>" +
            "<form action=\"" + WALK + "\" method=\"post\" enctype=\"multipart/form-data\"/>" +
            "    <textarea name=\"" + CODE_FIELD + "\" placeholder=\"Enter your public key\"" +
            "       rows=\"10\" cols=\"100\"/></textarea><br/>" +
            "    <input type=\"submit\" value=\"Compute the master secret\" name=\"submit\" />" +
            "    <input type=\"hidden\" name=\"" + TIMESTAMP_FIELD + "\" value=\"{{includeTimestamp}}\">" +
            "</form>" +
            "</center>").composeTemplateEngine();

    public AuthenticationHandler(String redirectResponseWalk) {
        this.redirectResponseWalk = redirectResponseWalk;
        this.template = new NetTemplateCreator().defineResourceName("basiccontenttemplate.html").assignLoader(getClass()).composeNetTemplate();
    }

    @Override
    public String grabWalk() {
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        @Bound("5") int i;
        @Inv("= contentsTemplateMap (+ c53 c57)") Map<String, String> contentsTemplateMap = new HashMap<>();
        @Inv("= templateMap (+ c54 c55 c59 c60)") Map<String, String> templateMap = new HashMap<>();

        String suppressTimestamp = grabUrlParam(httpExchange, "suppressTimestamp");
        if (suppressTimestamp == null || !suppressTimestamp.equals("true")) {
            c53: contentsTemplateMap.put("includeTimestamp", "true");
            c54: templateMap.put("timestamp", (new Date()).toString());
            c55: templateMap.put("duration", String.valueOf(obtainDuration(httpExchange)));
        } else {
            c57: contentsTemplateMap.put("includeTimestamp", "false");
        }
        c59: templateMap.put("contents", TEMPLATE_ENGINE.replaceTags(contentsTemplateMap));
        c60: templateMap.put("title", TITLE);

        return pullResponse(template.grabEngine().replaceTags(templateMap));
    }

    @Override
    protected HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        @Inv("= fieldNames (+ c68 c69)") Set<String> fieldNames = new HashSet<>();
        c68: fieldNames.add(CODE_FIELD);
        c69: fieldNames.add(TIMESTAMP_FIELD);
        Map<String, List<String>> fieldNameItems = MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames);
        String usersPublicCode = "";
        boolean includeTimestamp = true;
        if (fieldNameItems.get(CODE_FIELD) != null && fieldNameItems.get(CODE_FIELD).size() == 1) {
            usersPublicCode = fieldNameItems.get(CODE_FIELD).get(0);
        }

        if (fieldNameItems.get(TIMESTAMP_FIELD) != null && fieldNameItems.get(TIMESTAMP_FIELD).size() == 1) {
            String timestamp = fieldNameItems.get(TIMESTAMP_FIELD).get(0);
            if (timestamp.equals("false")) {
                includeTimestamp = false;
            }
        }
        String urlEnd = "";
        if (usersPublicCode != null) {
            urlEnd = usersPublicCode;
        }

        String suppressTimestamp = grabUrlParam(httpExchange, "suppressTimestamp");
        if (!includeTimestamp || (suppressTimestamp != null && suppressTimestamp.equals("true"))) {
            urlEnd += "?suppressTimestamp=true";
        }
        return grabRedirectResponse(redirectResponseWalk + "/" + urlEnd);
    }
}
