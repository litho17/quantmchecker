package simplevote_1.com.cyberpointllc.stac.webmaster;

public class NetworkSessionServiceCreator {
    private String applicationBaseName;
    private long sessionExpirationInMinutes;

    public NetworkSessionServiceCreator assignApplicationBaseName(String applicationBaseName) {
        this.applicationBaseName = applicationBaseName;
        return this;
    }

    public NetworkSessionServiceCreator defineSessionExpirationInMinutes(long sessionExpirationInMinutes) {
        this.sessionExpirationInMinutes = sessionExpirationInMinutes;
        return this;
    }

    public NetworkSessionService formNetworkSessionService() {
        return new NetworkSessionService(applicationBaseName, sessionExpirationInMinutes);
    }
}