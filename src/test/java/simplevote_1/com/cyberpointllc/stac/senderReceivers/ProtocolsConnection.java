package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import io.netty.channel.Channel;
import io.netty.util.AttributeKey;

import java.net.InetSocketAddress;

public final class ProtocolsConnection {

    public static final AttributeKey<ProtocolsConnection> CONNECTION_ATTR = new AttributeKey<>("CONNECTION_ATTR");

    private final Channel channel;
    private final ProtocolsPublicUnity theirUnity;

    /**
     * @param channel the netty channel to use for comms
     * @param theirUnity the identity of the other side of this connection
     */
    public ProtocolsConnection(Channel channel, ProtocolsPublicUnity theirUnity) {
        this.channel = channel;
        this.theirUnity = theirUnity;
    }

    /**
     * Sends str to the other side of the connection
     * @param str
     * @throws ProtocolsBad
     */
    public void write(String str) throws ProtocolsBad {
        write(str.getBytes());
    }

    /**
     * Sends bytes to the other side of the connection
     * @param bytes
     * @throws ProtocolsBad
     */
    public void write(byte[] bytes) throws ProtocolsBad {
        channel.writeAndFlush(bytes);
    }

    /**
     * Closes the connection gracefully
     * @throws ProtocolsBad
     */
    public void close() throws ProtocolsBad {
        try {
            channel.close().sync();
        } catch (Exception e) {
            throw new ProtocolsBad(e);
        }
    }

    public boolean isOpen() {
        return channel.isOpen();
    }

    /**
     * @return the identity of the other end of the connection
     */
    public ProtocolsPublicUnity fetchTheirUnity() {
        return theirUnity;
    }

    public String grabRemoteOriginString() {
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

        ProtocolsConnection connection = (ProtocolsConnection) o;
        if (!theirUnity.equals(connection.theirUnity)) return false;

        return true;

    }

    @Override
    // Note: this only uses the identity
    public int hashCode() {
        int outcome = theirUnity.hashCode();
        return outcome;
    }

    @Override
    public String toString(){
        return fetchTheirUnity().getId().toString();
    }

}
