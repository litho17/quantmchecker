package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionCreator;
import simplevote_1.com.cyberpointllc.stac.webmaster.Person;
import simplevote_1.com.cyberpointllc.stac.webmaster.PersonConductor;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSession;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;

import java.io.IOException;

/**
 * Always login the specified users
 */
public class NoLoginRarefy extends Filter {
    private final PersonConductor personConductor;
    private final NetworkSessionService networkSessionService;
    private final String personId;

    public NoLoginRarefy(PersonConductor personConductor, NetworkSessionService networkSessionService, String personId) {
        this.personConductor = personConductor;
        this.networkSessionService = networkSessionService;
        this.personId = personId;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        NetworkSession networkSession = networkSessionService.takeSession(httpExchange);
        Person person;
        if (networkSession == null) {
            person = personConductor.grabPersonByUnity(personId);
            networkSession = new NetworkSessionCreator().assignPersonId(personId).formNetworkSession();
            networkSessionService.addSession(httpExchange, networkSession);
            HttpGuideResponse response = AbstractHttpGuide.grabRedirectResponse(httpExchange.getRequestURI().toString());
            response.transmitResponse(httpExchange);
        } else {
            person = personConductor.grabPersonByUnity(networkSession.pullPersonId());
            if (person != null) {
                doRarefyHelper(httpExchange, chain, networkSession);
            } else {
                throw new IllegalArgumentException("No user associated with " + personId);
            }
        }
    }

    private void doRarefyHelper(HttpExchange httpExchange, Chain chain, NetworkSession networkSession) throws IOException {
        httpExchange.setAttribute("userId", networkSession.pullPersonId());
        chain.doFilter(httpExchange);
    }

    @Override
    public String description() {
        return "No Login Filter";
    }
}
