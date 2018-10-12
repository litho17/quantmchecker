package calculator_1.com.cyberpointllc.stac.netcontroller;

import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AuthenticationHandlerCreator;
import calculator_1.com.cyberpointllc.stac.permission.CodeExchangeController;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AbstractHttpHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.AuthenticationHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.LoginRefine;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.LoginHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.LogoutHandler;
import calculator_1.com.cyberpointllc.stac.netcontroller.handler.NoLoginRefine;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpContext;
import com.sun.net.httpserver.HttpServer;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.security.GeneralSecurityException;

public class NetController {
    private static final long DEFAULT_SESSION_TIMEOUT_IN_MINUTES = 1440L;

    private final HttpServer httpController;
    private final NetSessionService netSessionService;
    private final CodeExchangeController codeExchangeController;
    private final String passwordCode;
    private static final int SECONDS_TO_WAIT_TO_CLOSE = 0;

    private Filter loginRefine;

    /**
     * Creates an HTTP/S web server listening on the specified port.
     * This constructor omits authorization from the login workflow.
     * The specified appBaseName is used to construct a session cookie.
     * If the server is HTTPS, the specified resource stream and
     * password are needed to create a valid SSL context.  The stream
     * should point to valid Java KeyStore content and the password is
     * used to load the content (the KeyStore password). If using HTTP
     * the resourceStream should be null.
     * The optional passwordKeyFile points to a file that contains
     * the password used to encrypt user's passwords.
     * If the passwordKeyFile is <code>null</code>,
     * then passwords are not encrypted before comparison.
     *
     * @param appBaseName      name used to create a session cookie
     * @param port             used for server connections
     * @param resourceStream   InputStream to server KeyStore contents
     * @param resourcePassword password for KeyStore contents
     * @param passwordCodeFile  that contains key for encrypting passwords;
     *                         may be <code>null</code>
     * @throws IOException              if there is trouble creating the server
     * @throws GeneralSecurityException if there is trouble with the resource stream
     */
    public NetController(String appBaseName,
                         int port,
                         InputStream resourceStream,
                         String resourcePassword,
                         File passwordCodeFile)
            throws IOException, GeneralSecurityException {
        this(appBaseName, port, resourceStream, resourcePassword, passwordCodeFile, null);
    }

    /**
     * Creates an HTTP/S web server listening on the specified port.
     * The specified appBaseName is used to construct a session cookie.
     * If the server is HTTPS, the specified resource stream and
     * password are needed to create a valid SSL context.  The stream
     * should point to valid Java KeyStore content and the password is
     * used to load the content (the KeyStore password). If using HTTP
     * the resourceStream should be null.
     * The optional passwordKeyFile points to a file that contains
     * the password used to encrypt user's passwords.
     * If the passwordKeyFile is <code>null</code>,
     * then passwords are not encrypted before comparison.
     * The optional authKeyFile can be specified and points to a file
     * that contains the servers private key.
     * If the authKeyFile is not provided, then the authorization
     * step of logging in is omitted from the workflow.
     *
     * @param appBaseName      name used to create a session cookie
     * @param port             used for server connections
     * @param resourceStream   InputStream to server KeyStore contents
     * @param resourcePassword password for KeyStore contents
     * @param passwordCodeFile  that contains key for encrypting passwords;
     *                         may be <code>null</code>
     * @param permissionCodeFile      server private key used for authorization;
     *                         may be <code>null</code>
     * @throws IOException              if there is trouble creating the server
     * @throws GeneralSecurityException if there is trouble with the resource stream
     */
    public NetController(String appBaseName,
                         int port,
                         InputStream resourceStream,
                         String resourcePassword,
                         File passwordCodeFile,
                         File permissionCodeFile)
            throws IOException, GeneralSecurityException {
        httpController = NetControllerFactory.composeController(port, resourceStream, resourcePassword);
        // session times out after 10 minutes
        netSessionService = new NetSessionService(appBaseName, DEFAULT_SESSION_TIMEOUT_IN_MINUTES);

        // Read in private key used for password storage...
        passwordCode = (passwordCodeFile == null) ? null : FileUtils.readFileToString(passwordCodeFile);

        // Read in private key string for auth
        if (permissionCodeFile != null) {
            String permissionCode = FileUtils.readFileToString(permissionCodeFile);
            codeExchangeController = new CodeExchangeController(permissionCode);
        } else {
            codeExchangeController = null; // Authorization disabled
        }
    }

    public HttpServer pullController() {
        return httpController;
    }

    /**
     * Creates the default authorization handlers for the case
     * when there is only one user.
     * In this case, the specified user id is used to assign
     * all uses of this server as belonging to the associated user.
     *
     * @param userOverseer used to locate the specified user
     * @param userId      used to identify the active user
     */
    public void integrateDefaultPermissionHandlers(UserOverseer userOverseer, String userId) {
        loginRefine = new NoLoginRefine(userOverseer, netSessionService, userId);
    }

    public NetSessionService fetchNetSessionService() {
        return netSessionService;
    }

    public void stop() {
        httpController.stop(SECONDS_TO_WAIT_TO_CLOSE);
    }

    public void stop(int secondsToWaitToClose) {
        httpController.stop(secondsToWaitToClose);
    }

    public void start() {
        httpController.start();
    }

    public HttpContext composeContext(AbstractHttpHandler handler, boolean requirePermission) {
        HttpContext context = httpController.createContext(handler.grabWalk(), handler);

        if (requirePermission) {
            context.getFilters().add(loginRefine);
        }

        return context;
    }
}
