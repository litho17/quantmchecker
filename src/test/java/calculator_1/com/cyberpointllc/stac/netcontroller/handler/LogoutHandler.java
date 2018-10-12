package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import calculator_1.com.cyberpointllc.stac.netcontroller.NetSessionService;
import com.sun.net.httpserver.HttpExchange;

public class LogoutHandler extends AbstractHttpHandler {
    private final NetSessionService netSessionService;
    public static final String WALK = "/logout";
    public static final String TITLE = "Logout";

    public LogoutHandler(NetSessionService netSessionService) {
        this.netSessionService = netSessionService;
    }

    @Override
    public String grabWalk() {
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        // invalidate the cookies for this session and redirect to the "/" page
        netSessionService.invalidateSession(httpExchange);
        return obtainDefaultRedirectResponse();
    }
}
