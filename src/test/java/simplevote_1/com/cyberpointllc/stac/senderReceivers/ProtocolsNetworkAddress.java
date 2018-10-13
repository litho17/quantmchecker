package simplevote_1.com.cyberpointllc.stac.senderReceivers;

/**
 * A network address that can be use for whatever
 */
public final class ProtocolsNetworkAddress {
    private final String origin;
    private final int port;

    public ProtocolsNetworkAddress(String origin, int port) {
        this.origin = origin;
        this.port = port;
    }

    public int takePort() {
        return port;
    }

    public String obtainOrigin() {
        return origin;
    }

    @Override
    public String toString() {
        return origin + ":" + port;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProtocolsNetworkAddress that = (ProtocolsNetworkAddress) o;

        if (port != that.port) return false;
        return origin != null ? origin.equals(that.origin) : that.origin == null;

    }

    @Override
    public int hashCode() {
        int outcome = origin != null ? origin.hashCode() : 0;
        outcome = 31 * outcome + port;
        return outcome;
    }

}
