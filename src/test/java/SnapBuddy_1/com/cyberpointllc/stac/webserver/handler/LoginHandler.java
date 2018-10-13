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
        Map<String, String> templateMap = new  HashMap();
        templateMap.put("title", TITLE);
        templateMap.put("path", getPath());
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
            templateMap.put("masterSecret", masterSecret.toString());
        } else {
            templateMap.put("masterSecret", "Null");
        }
        String suppressTimeStamp = getUrlParam(httpExchange, "suppressTimestamp");
        if (StringUtils.isBlank(suppressTimeStamp) || !suppressTimeStamp.equalsIgnoreCase("true")) {
            templateMap.put("duration", String.valueOf(getDuration(httpExchange)));
            templateMap.put("timestamp", (new  Date()).toString());
        }
        return getResponse(templateEngine.replaceTags(templateMap));
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Set<String> fieldNames = new  HashSet();
        fieldNames.add(USERNAME_FIELD);
        fieldNames.add(PASSWORD_FIELD);
        Map<String, List<String>> loginCredentials = MultipartHelper.getMultipartValues(httpExchange, fieldNames);
        List<String> usernames = loginCredentials.get(USERNAME_FIELD);
        List<String> passwords = loginCredentials.get(PASSWORD_FIELD);
        int conditionObj2 = 1;
        if ((usernames != null) && (usernames.size() == conditionObj2) && (passwords != null) && (passwords.size() == 1)) {
            String username = usernames.get(0);
            String password = passwords.get(0);
            // password is stored encrypted, so we should encrypt this before comparing...
            String encryptedPw = DESHelper.getEncryptedString(password, passwordKey);
            User currentUser = userManager.getUserByUsername(username);
            if (currentUser != null && currentUser.matches(username, encryptedPw)) {
                WebSession webSession = new  WebSession(currentUser.getIdentity());
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
