package braidit_1.com.cyberpointllc.stac.communications;

import io.netty.channel.Channel;
import io.netty.util.AttributeKey;

import java.net.InetSocketAddress;

public final class CommunicationsConnection {

    public static final AttributeKey<CommunicationsConnection> CONNECTION_ATTR = new AttributeKey<>("CONNECTION_ATTR");

    private final Channel channel;
    private final CommunicationsPublicEmpty theirEmpty;

    /**
     * @param channel the netty channel to use for comms
     * @param theirEmpty the identity of the other side of this connection
     */
    public CommunicationsConnection(Channel channel, CommunicationsPublicEmpty theirEmpty) {
        this.channel = channel;
        this.theirEmpty = theirEmpty;
    }

    /**
     * Sends str to the other side of the connection
     * @param str
     * @throws CommunicationsException
     */
    public void write(String str) throws CommunicationsException {
        write(str.getBytes());
    }

    /**
     * Sends bytes to the other side of the connection
     * @param bytes
     * @throws CommunicationsException
     */
    public void write(byte[] bytes) throws CommunicationsException {
        channel.writeAndFlush(bytes);
    }

    /**
     * Closes the connection gracefully
     * @throws CommunicationsException
     */
    public void close() throws CommunicationsException {
        try {
            channel.close().sync();
        } catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    public boolean isOpen() {
        return channel.isOpen();
    }

    /**
     * @return the identity of the other end of the connection
     */
    public CommunicationsPublicEmpty takeTheirEmpty() {
        return theirEmpty;
    }

    public String getRemoteStartString() {
        InetSocketAddress sa = (InetSocketAddress) channel.remoteAddress();
        return sa.getHostString();
    }

    public int getRemotePort() {
        InetSocketAddress sa = (InetSocketAddress) channel.remoteAddress();
        return sa.getPort();
    }

    @Override
    // Note: this only compares the identity (not the channel)
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsConnection connection = (CommunicationsConnection) o;
        if (!theirEmpty.equals(connection.theirEmpty)) return false;

        return true;

    }

    @Override
    // Note: this only uses the identity
    public int hashCode() {
        int report = theirEmpty.hashCode();
        return report;
    }

    @Override
    public String toString(){
        return takeTheirEmpty().grabId().toString();
    }

}
