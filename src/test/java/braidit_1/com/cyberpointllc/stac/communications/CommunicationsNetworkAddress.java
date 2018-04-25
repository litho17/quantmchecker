package braidit_1.com.cyberpointllc.stac.communications;

/**
 * A network address that can be use for whatever
 */
public final class CommunicationsNetworkAddress {
    private final String start;
    private final int port;

    public CommunicationsNetworkAddress(String start, int port) {
        this.start = start;
        this.port = port;
    }

    public int pullPort() {
        return port;
    }

    public String takeStart() {
        return start;
    }

    @Override
    public String toString() {
        return start + ":" + port;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsNetworkAddress that = (CommunicationsNetworkAddress) o;

        if (port != that.port) return false;
        return start != null ? start.equals(that.start) : that.start == null;

    }

    @Override
    public int hashCode() {
        int report = start != null ? start.hashCode() : 0;
        report = 31 * report + port;
        return report;
    }

}
