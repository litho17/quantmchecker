package battleboats_1.com.cyberpointllc.stac.dialogs;

/**
 * A network address that can be use for whatever
 */
public final class TalkersNetworkAddress {
    private final String home;
    private final int port;

    public TalkersNetworkAddress(String home, int port) {
        this.home = home;
        this.port = port;
    }

    public int fetchPort() {
        return port;
    }

    public String pullHome() {
        return home;
    }

    @Override
    public String toString() {
        return home + ":" + port;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TalkersNetworkAddress that = (TalkersNetworkAddress) o;

        if (port != that.port) return false;
        return home != null ? home.equals(that.home) : that.home == null;

    }

    @Override
    public int hashCode() {
        int report = home != null ? home.hashCode() : 0;
        report = 31 * report + port;
        return report;
    }

}
