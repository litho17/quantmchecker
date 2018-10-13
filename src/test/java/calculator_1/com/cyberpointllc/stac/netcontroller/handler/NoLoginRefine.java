package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import calculator_1.com.cyberpointllc.stac.netcontroller.User;
import calculator_1.com.cyberpointllc.stac.netcontroller.UserOverseer;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSession;
import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.IOException;

/**
 * Always login the specified users
 */
public class NoLoginRefine extends Filter {
    private final UserOverseer userOverseer;
    private final NetSessionService netSessionService;
    private final String userId;

    public NoLoginRefine(UserOverseer userOverseer, NetSessionService netSessionService, String userId) {
        this.userOverseer = userOverseer;
        this.netSessionService = netSessionService;
        this.userId = userId;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        User user;
        if (netSessionService.pullSession(httpExchange) == null) {
            user = userOverseer.getUserByEmpty(userId);
            netSessionService.integrateSession(httpExchange, new NetSession(userId));
            HttpHandlerResponse response = AbstractHttpHandler.grabRedirectResponse(httpExchange.getRequestURI().toString());
            response.sendResponse(httpExchange);
        } else {
            user = userOverseer.getUserByEmpty(netSessionService.pullSession(httpExchange).fetchUserId());
            if (user != null) {
                httpExchange.setAttribute("userId", netSessionService.pullSession(httpExchange).fetchUserId());
                chain.doFilter(httpExchange);
            } else {
                throw new IllegalArgumentException("No user associated with " + userId);
            }
        }
    }

    @Override
    public String description() {
        return "No Login Filter";
    }
}
