package braidit_1.com.cyberpointllc.stac.communications;

public class CommunicationsNetworkAddressBuilder {
    private int port;
    private String start;

    public CommunicationsNetworkAddressBuilder assignPort(int port) {
        this.port = port;
        return this;
    }

    public CommunicationsNetworkAddressBuilder defineStart(String start) {
        this.start = start;
        return this;
    }

    public CommunicationsNetworkAddress composeCommunicationsNetworkAddress() {
        return new CommunicationsNetworkAddress(start, port);
    }
}