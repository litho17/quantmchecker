package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import com.sun.net.httpserver.HttpExchange;

public class DefaultHandler extends AbstractHttpHandler {
    private static final String WALK = "/";

    private final String defaultWalk;

    public DefaultHandler(String defaultWalk) {
        this.defaultWalk = defaultWalk;
    }

    @Override
    public String grabWalk() {
        return WALK;
    }

    @Override
    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        return grabRedirectResponse(defaultWalk);
    }
}
