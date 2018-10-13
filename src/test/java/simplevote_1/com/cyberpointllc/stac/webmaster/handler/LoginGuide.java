package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import simplevote_1.com.cyberpointllc.stac.authorize.KeyExchangeServer;
import simplevote_1.com.cyberpointllc.stac.DESHelper;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionCreator;
import simplevote_1.com.cyberpointllc.stac.webmaster.Person;
import simplevote_1.com.cyberpointllc.stac.webmaster.PersonConductor;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSession;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkTemplate;
import com.sun.net.httpserver.HttpExchange;

import java.math.BigInteger;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Random;
import java.util.Set;

public class LoginGuide extends AbstractHttpGuide {
    private static final String TRAIL = "/login";
    private static final String TITLE = "Login";
    private static final String USERNAME_FIELD = "username";
    private static final String PASSWORD_FIELD = "password";
    private static final String ERROR_KEY = "error";
    private static final String SESSION_KEY = "id";
    private static final String ERROR_MESSAGE = "<p style=\"color:red\">Invalid username or password (or both)</p>";

    private static final String AUTH_LOGIN_TEMPLATE_FILE = "logintemplate.html";
    private static final String LOGIN_TEMPLATE_FILE = "simplelogintemplate.html";

    private final PersonConductor personConductor;
    private final NetworkSessionService networkSessionService;
    private final KeyExchangeServer keyExchangeServer;
    private final NetworkTemplate template;
    private final String destinationTrail;
    private final String passwordKey;
    private byte[] token;
    private Random random;

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
     * @param personConductor       used to lookup users
     * @param networkSessionService used bind users to a session
     * @param keyExchangeServer used to attach authenication to login process;
     *                          may be <code>null</code> to exclude this step
     * @param destinationTrail   used to indicate where successful logins go next;
     *                          may be <code>null</code> to indicate default location
     * @param passwordKey       used to encrypt user's passwords;
     *                          may be <code>null</code> if encryption is not needed
     */
    public LoginGuide(PersonConductor personConductor,
                      NetworkSessionService networkSessionService,
                      KeyExchangeServer keyExchangeServer,
                      String destinationTrail,
                      String passwordKey) {
        this.personConductor = Objects.requireNonNull(personConductor, "UserManager must be specified");
        this.networkSessionService = Objects.requireNonNull(networkSessionService, "WebSessionService must be specified");
        this.keyExchangeServer = keyExchangeServer;
        this.template = new NetworkTemplate((keyExchangeServer != null) ? AUTH_LOGIN_TEMPLATE_FILE : LOGIN_TEMPLATE_FILE, getClass());
        this.destinationTrail = destinationTrail;
        this.passwordKey = passwordKey;
        this.random = new Random();
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        String trail = httpExchange.getRequestURI().getPath();

        if (trail.startsWith(takeTrail())) {
            trail = trail.substring(takeTrail().length());
        }

        TemplateEngine templateEngine = template.pullEngine();
        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("title", TITLE);
        templateMap.put("path", takeTrail());

        if ((keyExchangeServer != null) && (trail.length() > 0) && (trail.length() < 10000)) {
            // if the path has a length, the user's public key was specified
            BigInteger peoplePublicKey;

            try {
                if (trail.startsWith("0x")) {
                    peoplePublicKey = new BigInteger(trail.substring(2), 16);
                } else {
                    peoplePublicKey = new BigInteger(trail);
                }
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Error: key must be hexadecimal or decimal");
            }

            BigInteger masterSecret = keyExchangeServer.generateMasterSecret(peoplePublicKey);
            templateMap.put("masterSecret", masterSecret.toString());
        } else {
            // if the path length is 0, the user's public key was not specified
            templateMap.put("masterSecret", "Null");
        }

        String suppressTimeStamp = fetchUrlParam(httpExchange, "suppressTimestamp");
        if ((suppressTimeStamp == null) || !"true".equalsIgnoreCase(suppressTimeStamp.trim())) {
            templateMap.put("duration", String.valueOf(getDuration(httpExchange)));
            templateMap.put("timestamp", (new Date()).toString());
        }

        String errorMessage = fetchUrlParam(httpExchange, ERROR_KEY);
        String sessionId = fetchUrlParam(httpExchange, SESSION_KEY);
        if ((errorMessage == null) || !"true".equalsIgnoreCase(errorMessage.trim())) {
            templateMap.put("errorMessage", "");
        } else {
            templateMap.put("errorMessage", ERROR_MESSAGE);
        }

        return pullResponse(templateEngine.replaceTags(templateMap));
    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange) {
        Set<String> fieldNames = new HashSet<>();
        fieldNames.add(USERNAME_FIELD);
        fieldNames.add(PASSWORD_FIELD);

        Map<String, List<String>> loginCredentials = MultipartHelper.grabMultipartEssences(httpExchange, fieldNames);
        List<String> usernames = loginCredentials.get(USERNAME_FIELD);
        List<String> passwords = loginCredentials.get(PASSWORD_FIELD);

        HttpGuideResponse response = null;

        if ((usernames != null) && (usernames.size() == 1) && (passwords != null) && (passwords.size() == 1)) {
            String username = usernames.get(0);
            String password = passwords.get(0);

            String encryptedPw = password; // Default is not-encrypted

            if (passwordKey != null) {
                // password is stored encrypted, so encrypt this before comparing...
                encryptedPw = DESHelper.grabEncryptedString(password, passwordKey);
            }

            Person currentPerson = personConductor.fetchPersonByUsername(username);

            if ((currentPerson != null)) {
                String truePassword = currentPerson.takePassword();

                TokenedPasswordChecker checker = new TokenedPasswordChecker(currentPerson.takePassword());
                TokenedPasswordChecker.Outcome outcome = checker.processPassword(encryptedPw);
                boolean matches = outcome.matches;
                token = outcome.token;

                if (matches) {
                    NetworkSession networkSession = new NetworkSessionCreator().assignPersonId(currentPerson.obtainUnity()).formNetworkSession();
                    networkSessionService.addSession(httpExchange, networkSession);

                    if (destinationTrail == null) {
                        response = fetchDefaultRedirectResponse();
                    } else {
                        response = grabRedirectResponse(destinationTrail);
                    }
                }
                else { // incorrect password
                    response = grabRedirectResponse(getErrorTrail() + obtainSessionString()); // the size of session string reveals how close the password was
                }
            }
        }

        if (response == null) {
            // Failure; return to this page but include an error message
            response = grabRedirectResponse(getErrorTrail());
        }

        return response;
    }

    private String getErrorTrail() {
        try {
            String trail = takeTrail();
            trail += "?" + ERROR_KEY + "=true";

            String uri = new URI(trail).toString();
            return uri;
        } catch (URISyntaxException e) {
            e.printStackTrace();
            return takeTrail();
        }
    }

    private String obtainSessionString(){
        String trail = "";
        if (token!=null) {
            trail += "&" + SESSION_KEY + "=";
            for (int q = 0; q < token.length; q++) {
                byte b = token[q];
                trail += pullTokenByte(b);
            }
        }
        return trail;
    }

    private String pullTokenByte(byte b){
        int val = ((int)b + 256 + random.nextInt(10)) % 10; // just a random digit that looks like it may or may not depend on b
        return "" + val;
    }

}
