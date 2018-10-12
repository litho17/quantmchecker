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
 * Determines if the exchange is part of an existing active session.
 * If so, the next item in the chain is called; otherwise, the
 * call is redirected to the authentication handler path.
 */
public class LoginRefine extends Filter {
    private final UserOverseer userOverseer;
    private final NetSessionService netSessionService;
    private final String authenticationHandlerWalk;

    public LoginRefine(UserOverseer userOverseer, NetSessionService netSessionService, String authenticationHandlerWalk) {
        this.userOverseer = userOverseer;
        this.netSessionService = netSessionService;
        this.authenticationHandlerWalk = authenticationHandlerWalk;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        @InvUnk("Nested lists") NetSession netSession = netSessionService.pullSession(httpExchange);
        User user = null;
        if (netSession != null) {
            user = userOverseer.getUserByEmpty(netSession.fetchUserId());
        }
        if (user != null) {
            doRefineAdviser(httpExchange, chain, netSession);
        } else {
            HttpHandlerResponse response = AbstractHttpHandler.grabRedirectResponse(authenticationHandlerWalk);
            response.sendResponse(httpExchange);
        }
    }

    private void doRefineAdviser(HttpExchange httpExchange, Chain chain, NetSession netSession) throws IOException {
        httpExchange.setAttribute("userId", netSession.fetchUserId());
        chain.doFilter(httpExchange);
    }

    @Override
    public String description() {
        return "Login Filter";
    }
}
