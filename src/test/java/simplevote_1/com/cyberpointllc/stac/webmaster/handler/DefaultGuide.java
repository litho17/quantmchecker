package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import com.sun.net.httpserver.HttpExchange;

public class DefaultGuide extends AbstractHttpGuide {
    private static final String TRAIL = "/";

    private final String defaultTrail;

    public DefaultGuide(String defaultTrail) {
        this.defaultTrail = defaultTrail;
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        return grabRedirectResponse(defaultTrail);
    }
}
