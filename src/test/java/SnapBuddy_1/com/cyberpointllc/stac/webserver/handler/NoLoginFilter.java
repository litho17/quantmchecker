package SnapBuddy_1.com.cyberpointllc.stac.webserver.handler;

import SnapBuddy_1.com.cyberpointllc.stac.webserver.User;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.UserManager;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSession;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSessionService;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;
import java.io.IOException;

/**
 * Always login the specified users
 */
public class NoLoginFilter extends Filter {

    private final UserManager userManager;

    private final WebSessionService webSessionService;

    private final String userId;

    public NoLoginFilter(UserManager userManager, WebSessionService webSessionService, String userId) {
        this.userManager = userManager;
        this.webSessionService = webSessionService;
        this.userId = userId;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        User user;
        if (webSessionService.getSession(httpExchange) == null) {
            user = userManager.getUserByIdentity(userId);
            webSessionService.addSession(httpExchange, new  WebSession(userId));
            HttpHandlerResponse response = AbstractHttpHandler.getRedirectResponse(httpExchange.getRequestURI().toString());
            response.sendResponse(httpExchange);
        } else {
            user = userManager.getUserByIdentity(webSessionService.getSession(httpExchange).getUserId());
            if (user != null) {
                httpExchange.setAttribute("userId", webSessionService.getSession(httpExchange).getUserId());
                chain.doFilter(httpExchange);
            } else {
                throw new  IllegalArgumentException("No user associated with " + userId);
            }
        }
    }

    @Override
    public String description() {
        return "No Login Filter";
    }
}
