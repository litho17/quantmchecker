package braidit_1.com.cyberpointllc.stac.communications;

public interface CommunicationsManager {
    /**
     * Called when data arrives on the connection
     * @param connection the connection the data came from
     * @param data the data
     * @throws CommunicationsException
     */
    void handle(CommunicationsConnection connection, byte[] data) throws CommunicationsException;

    /**
     * Called when a new connection has been established and it has been authenticated
     * @param connection
     * @throws CommunicationsException
     */
    void newConnection(CommunicationsConnection connection) throws CommunicationsException;

    /**
     * Called when a connection is closed
     * @param connection
     * @throws CommunicationsException
     */
    void closedConnection(CommunicationsConnection connection) throws CommunicationsException;
}
