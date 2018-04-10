package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.webserver.handler.AbstractHttpHandler;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;

public class DefaultHandler extends AbstractHttpHandler {

    private static final String PATH = "/";

    private final String defaultPath;

    public DefaultHandler(String defaultPath) {
        this.defaultPath = defaultPath;
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        return getRedirectResponse(defaultPath);
    }
}
