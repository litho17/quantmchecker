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
        @InvUnk("Nested lists") NetSession netSession = netSessionService.pullSession(httpExchange);
        User user;
        if (netSession == null) {
            user = userOverseer.getUserByEmpty(userId);
            netSession = new NetSession(userId);
            netSessionService.integrateSession(httpExchange, netSession);
            HttpHandlerResponse response = AbstractHttpHandler.grabRedirectResponse(httpExchange.getRequestURI().toString());
            response.sendResponse(httpExchange);
        } else {
            user = userOverseer.getUserByEmpty(netSession.fetchUserId());
            if (user != null) {
                httpExchange.setAttribute("userId", netSession.fetchUserId());
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
