package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import simplevote_1.com.cyberpointllc.stac.webmaster.Person;
import simplevote_1.com.cyberpointllc.stac.webmaster.PersonConductor;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSession;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;

import java.io.IOException;

/**
 * Determines if the exchange is part of an existing active session.
 * If so, the next item in the chain is called; otherwise, the
 * call is redirected to the authentication handler path.
 */
public class LoginRarefy extends Filter {
    private final PersonConductor personConductor;
    private final NetworkSessionService networkSessionService;
    private final String authenticationGuideTrail;

    public LoginRarefy(PersonConductor personConductor, NetworkSessionService networkSessionService, String authenticationGuideTrail) {
        this.personConductor = personConductor;
        this.networkSessionService = networkSessionService;
        this.authenticationGuideTrail = authenticationGuideTrail;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        NetworkSession networkSession = networkSessionService.takeSession(httpExchange);
        Person person = null;
        if (networkSession != null) {
            person = personConductor.grabPersonByUnity(networkSession.pullPersonId());
        }
        if (person != null) {
            httpExchange.setAttribute("userId", networkSession.pullPersonId());
            chain.doFilter(httpExchange);
        } else {
            HttpGuideResponse response = AbstractHttpGuide.grabRedirectResponse(authenticationGuideTrail);
            response.transmitResponse(httpExchange);
        }
    }

    @Override
    public String description() {
        return "Login Filter";
    }
}
