package simplevote_1.com.cyberpointllc.stac.senderReceivers;

public interface ProtocolsGuide {
    /**
     * Called when data arrives on the connection
     * @param connection the connection the data came from
     * @param data the data
     * @throws ProtocolsBad
     */
    void handle(ProtocolsConnection connection, byte[] data) throws ProtocolsBad;

    /**
     * Called when a new connection has been established and it has been authenticated
     * @param connection
     * @throws ProtocolsBad
     */
    void newConnection(ProtocolsConnection connection) throws ProtocolsBad;

    /**
     * Called when a connection is closed
     * @param connection
     * @throws ProtocolsBad
     */
    void closedConnection(ProtocolsConnection connection) throws ProtocolsBad;
}
