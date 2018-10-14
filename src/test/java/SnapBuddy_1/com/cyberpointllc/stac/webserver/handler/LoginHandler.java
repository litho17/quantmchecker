package SnapBuddy_1.com.cyberpointllc.stac.webserver.handler;

import SnapBuddy_1.com.cyberpointllc.stac.common.DESHelper;
import SnapBuddy_1.com.cyberpointllc.stac.auth.KeyExchangeServer;
import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.User;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.UserManager;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSession;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSessionService;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebTemplate;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.math.BigInteger;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class LoginHandler extends AbstractHttpHandler {

    private static final String PATH = "/login";

    private static final String TITLE = "Login";

    private static final String USERNAME_FIELD = "username";

    private static final String PASSWORD_FIELD = "password";

    private final UserManager userManager;

    private final WebSessionService webSessionService;

    private final KeyExchangeServer keyExchangeServer;

    private final WebTemplate template;

    private final String destinationPath;

    private final String passwordKey;

    public LoginHandler(UserManager userManager, WebSessionService webSessionService, KeyExchangeServer keyExchangeServer, String destinationPath, String passwordKey) {
        this.userManager = userManager;
        this.webSessionService = webSessionService;
        this.keyExchangeServer = keyExchangeServer;
        this.template = new  WebTemplate("logintemplate.html", getClass());
        this.destinationPath = destinationPath;
        this.passwordKey = passwordKey;
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        String path = httpExchange.getRequestURI().getPath();
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
            // Check for slash after the path
            if ((path.length() > 0) && path.startsWith("/")) {
                path = path.substring(1);
            }
        }
        TemplateEngine templateEngine = template.getEngine();
        @Bound("5") int i;
        @Inv("= templateMap (+ c74 c75 c91 c93 c97 c98)") Map<String, String> templateMap = new  HashMap();
        c74: templateMap.put("title", TITLE);
        c75: templateMap.put("path", getPath());
        int conditionObj0 = 0;
        int conditionObj1 = 10000;
        // was specified
        if (path.length() > conditionObj0 && path.length() < conditionObj1) {
            BigInteger usersPublicKey;
            try {
                if (path.startsWith("0x")) {
                    usersPublicKey = new  BigInteger(path.substring(2), 16);
                } else {
                    usersPublicKey = new  BigInteger(path);
                }
            } catch (NumberFormatException e) {
                throw new  IllegalArgumentException("Error: key must be hexadecimal or decimal");
            }
            BigInteger masterSecret = keyExchangeServer.generateMasterSecret(usersPublicKey);
            c91: templateMap.put("masterSecret", masterSecret.toString());
        } else {
            c93: templateMap.put("masterSecret", "Null");
        }
        String suppressTimeStamp = getUrlParam(httpExchange, "suppressTimestamp");
        if (StringUtils.isBlank(suppressTimeStamp) || !suppressTimeStamp.equalsIgnoreCase("true")) {
            c97: templateMap.put("duration", String.valueOf(getDuration(httpExchange)));
            c98: templateMap.put("timestamp", (new  Date()).toString());
        }
        return getResponse(templateEngine.replaceTags(templateMap));
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        @Inv("= fieldNames (+ c106 c107)") Set<String> fieldNames = new  HashSet();
        c106: fieldNames.add(USERNAME_FIELD);
        c107: fieldNames.add(PASSWORD_FIELD);
        @InvUnk("Nested lists") Map<String, List<String>> loginCredentials = MultipartHelper.getMultipartValues(httpExchange, fieldNames);
        int conditionObj2 = 1;
        if ((loginCredentials.get(USERNAME_FIELD) != null) && (loginCredentials.get(USERNAME_FIELD).size() == conditionObj2) && (loginCredentials.get(PASSWORD_FIELD) != null) && (loginCredentials.get(PASSWORD_FIELD).size() == 1)) {
            String username = loginCredentials.get(USERNAME_FIELD).get(0);
            String password = loginCredentials.get(PASSWORD_FIELD).get(0);
            // password is stored encrypted, so we should encrypt this before comparing...
            String encryptedPw = DESHelper.getEncryptedString(password, passwordKey);
            User currentUser = userManager.getUserByUsername(username);
            if (currentUser != null && currentUser.matches(username, encryptedPw)) {
                @Inv("= webSession.propertyMap 0") WebSession webSession = new  WebSession(currentUser.getIdentity());
                webSessionService.addSession(httpExchange, webSession);
                if (destinationPath == null) {
                    return getDefaultRedirectResponse();
                } else {
                    return getRedirectResponse(destinationPath);
                }
            }
        }
        // if we've gotten this far, it means the user didn't enter a correct username/password
        throw new  IllegalArgumentException("Invalid username or password (or both)");
    }
}
