package SnapBuddy_1.com;

import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSession;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSessionService;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.NoLoginFilter;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;

/**
 * @author Tianhan Lu
 */
public class Driver {
    WebSessionService webSessionService;
    HttpExchange httpExchange;
    WebSession session;
    NoLoginFilter noLoginFilter;
    Filter.Chain chain;
    public void main() throws Exception {
        webSessionService.addSession(httpExchange, session);
        noLoginFilter.doFilter(httpExchange, chain);
    }
}
