package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import com.sun.net.httpserver.HttpExchange;

public class LogoutGuide extends AbstractHttpGuide {
    private final NetworkSessionService networkSessionService;
    public static final String TRAIL = "/logout";
    public static final String TITLE = "Logout";

    public LogoutGuide(NetworkSessionService networkSessionService) {
        this.networkSessionService = networkSessionService;
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        // invalidate the cookies for this session and redirect to the "/" page
        networkSessionService.invalidateSession(httpExchange);
        return fetchDefaultRedirectResponse();
    }
}
