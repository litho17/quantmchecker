package simplevote_1.com.cyberpointllc.stac.webmaster;

public class NetworkSessionCreator {
    private String personId;

    public NetworkSessionCreator assignPersonId(String personId) {
        this.personId = personId;
        return this;
    }

    public NetworkSession formNetworkSession() {
        return new NetworkSession(personId);
    }
}