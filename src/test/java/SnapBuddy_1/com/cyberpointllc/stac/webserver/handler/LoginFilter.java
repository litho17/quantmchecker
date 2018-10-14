package SnapBuddy_1.com.cyberpointllc.stac.webserver.handler;

import SnapBuddy_1.com.cyberpointllc.stac.webserver.User;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.UserManager;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSession;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSessionService;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;
import java.io.IOException;

/**
 * Determines if the exchange is part of an existing active session.
 * If so, the next item in the chain is called; otherwise, the
 * call is redirected to the authentication handler path.
 */
public class LoginFilter extends Filter {

    private final UserManager userManager;

    private final WebSessionService webSessionService;

    private final String authenticationHandlerPath;

    public LoginFilter(UserManager userManager, WebSessionService webSessionService, String authenticationHandlerPath) {
        this.userManager = userManager;
        this.webSessionService = webSessionService;
        this.authenticationHandlerPath = authenticationHandlerPath;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        User user = null;
        if (webSessionService.getSession(httpExchange) != null) {
            user = userManager.getUserByIdentity(webSessionService.getSession(httpExchange).getUserId());
        }
        if (user != null) {
            httpExchange.setAttribute("userId", webSessionService.getSession(httpExchange).getUserId());
            chain.doFilter(httpExchange);
        } else {
            HttpHandlerResponse response = AbstractHttpHandler.getRedirectResponse(authenticationHandlerPath);
            response.sendResponse(httpExchange);
        }
    }

    @Override
    public String description() {
        return "Login Filter";
    }
}
