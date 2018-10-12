package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplateCreator;
import calculator_1.com.cyberpointllc.stac.permission.CodeExchangeController;
import calculator_1.com.cyberpointllc.stac.DESAssistant;
import calculator_1.com.cyberpointllc.stac.template.TemplateEngine;
import calculator_1.com.cyberpointllc.stac.netcontroller.User;
import calculator_1.com.cyberpointllc.stac.netcontroller.UserOverseer;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSession;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetTemplate;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.math.BigInteger;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class LoginHandler extends AbstractHttpHandler {
    public static final String WALK = "/login";
    private static final String TITLE = "Login";
    private static final String USERNAME_FIELD = "username";
    private static final String PASSWORD_FIELD = "password";
    private static final String ERROR_CODE = "error";
    private static final String ERROR_MESSAGE = "<p style=\"color:red\">Invalid username or password (or both)</p>";

    private static final String PERMISSION_LOGIN_TEMPLATE_FILE = "logintemplate.html";
    private static final String LOGIN_TEMPLATE_FILE = "simplelogintemplate.html";

    // private final UserOverseer userOverseer;
    private final NetSessionService netSessionService;
    private final CodeExchangeController codeExchangeController;
    private final NetTemplate template;
    private final String destinationWalk;
    private final String passwordCode;

    /**
     * Creates a login handler to manage the username and password page.
     * The specified user manager is used to lookup the user.
     * The specified web session service is used to bind the user's
     * session to a client-side cookie.
     * An optional key exchange server is used to add the DH
     * authentication process to the login workflow.
     * The optional destination path indicates where successful logins
     * should be redirected.  If not specified, the default destination
     * is used instead.
     * The specified password key is used encrypt inbound passwords.
     * If this key is <code>null</code>, encryption of passwords is omitted.
     *
     * @param userOverseer       used to lookup users
     * @param netSessionService used bind users to a session
     * @param codeExchangeController used to attach authenication to login process;
     *                          may be <code>null</code> to exclude this step
     * @param destinationWalk   used to indicate where successful logins go next;
     *                          may be <code>null</code> to indicate default location
     * @param passwordCode       used to encrypt user's passwords;
     *                          may be <code>null</code> if encryption is not needed
     */
    public LoginHandler(UserOverseer userOverseer,
                        NetSessionService netSessionService,
                        CodeExchangeController codeExchangeController,
                        String destinationWalk,
                        String passwordCode) {
        // this.userOverseer = Objects.requireNonNull(userOverseer, "UserManager must be specified");
        this.netSessionService = Objects.requireNonNull(netSessionService, "WebSessionService must be specified");
        this.codeExchangeController = codeExchangeController;
        this.template = new NetTemplateCreator().defineResourceName((codeExchangeController != null) ? PERMISSION_LOGIN_TEMPLATE_FILE : LOGIN_TEMPLATE_FILE).assignLoader(getClass()).composeNetTemplate();
        this.destinationWalk = destinationWalk;
        this.passwordCode = passwordCode;
    }

    @Override
    public String grabWalk() {
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        String walk = httpExchange.getRequestURI().getPath();

        if (walk.startsWith(grabWalk())) {
            walk = walk.substring(grabWalk().length());

            // Check for slash after the path
            if ((walk.length() > 0) && walk.startsWith("/")) {
                walk = walk.substring(1);
            }
        }

        TemplateEngine templateEngine = template.grabEngine();
        @Bound("6") int i;
        @Inv("= templateMap (+ c102 c103 c120 c123 c128 c129 c134 c136)") Map<String, String> templateMap = new HashMap<>();
        c102: templateMap.put("title", TITLE);
        c103: templateMap.put("path", grabWalk());

        if ((codeExchangeController != null) && (walk.length() > 0) && (walk.length() < 10000)) {
            // if the path has a length, the user's public key was specified
            BigInteger usersPublicCode;

            try {
                if (walk.startsWith("0x")) {
                    usersPublicCode = new BigInteger(walk.substring(2), 16);
                } else {
                    usersPublicCode = new BigInteger(walk);
                }
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Error: key must be hexadecimal or decimal");
            }

            BigInteger masterSecret = codeExchangeController.generateMasterSecret(usersPublicCode);
            c120: templateMap.put("masterSecret", masterSecret.toString());
        } else {
            // if the path length is 0, the user's public key was not specified
            c123: templateMap.put("masterSecret", "Null");
        }

        String suppressTimeStamp = grabUrlParam(httpExchange, "suppressTimestamp");
        if ((suppressTimeStamp == null) || !"true".equalsIgnoreCase(suppressTimeStamp.trim())) {
            c128: templateMap.put("duration", String.valueOf(obtainDuration(httpExchange)));
            c129: templateMap.put("timestamp", (new Date()).toString());
        }

        String errorMessage = grabUrlParam(httpExchange, ERROR_CODE);
        if ((errorMessage == null) || !"true".equalsIgnoreCase(errorMessage.trim())) {
            c134: templateMap.put("errorMessage", "");
        } else {
            c136: templateMap.put("errorMessage", ERROR_MESSAGE);
        }

        return pullResponse(templateEngine.replaceTags(templateMap));
    }

    @Override
    @Summary({"this.netSessionService.sessions", "1", "this.netSessionService.times", "1"})
    public HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        @Bound("2") int i;
        @Inv("= fieldNames (+ c147 c148)") Set<String> fieldNames = new HashSet<>();
        c147: fieldNames.add(USERNAME_FIELD);
        c148: fieldNames.add(PASSWORD_FIELD);


        HttpHandlerResponse response = null;

        if ((MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(USERNAME_FIELD) != null) && (MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(USERNAME_FIELD).size() == 1) && (MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(PASSWORD_FIELD) != null) && (MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(PASSWORD_FIELD).size() == 1)) {
            String username = MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(USERNAME_FIELD).get(0);
            String password = MultipartAssistant.fetchMultipartValues(httpExchange, fieldNames).get(PASSWORD_FIELD).get(0);

            String encryptedPw = password; // Default is not-encrypted

            if (passwordCode != null) {
                // password is stored encrypted, so encrypt this before comparing...
                encryptedPw = DESAssistant.pullEncryptedString(password, passwordCode);
            }

            User currentUser = null; // userOverseer.takeUserByUsername(username);

            if ((currentUser != null) && currentUser.matches(username, encryptedPw)) {
                @Inv("= netSession.propertyMap 0") NetSession netSession = new NetSession(currentUser.takeEmpty());
                netSessionService.integrateSession(httpExchange, netSession);

                if (destinationWalk == null) {
                    response = obtainDefaultRedirectResponse();
                } else {
                    response = grabRedirectResponse(destinationWalk);
                }
            }
        }

        if (response == null) {
            // Failure; return to this page but include an error message
            response = grabRedirectResponse(pullErrorWalk());
        }

        return response;
    }

    private String pullErrorWalk() {
        try {
            return new URI(grabWalk() + "?" + ERROR_CODE + "=true").toString();
        } catch (URISyntaxException e) {
            e.printStackTrace();
            return grabWalk();
        }
    }
}
