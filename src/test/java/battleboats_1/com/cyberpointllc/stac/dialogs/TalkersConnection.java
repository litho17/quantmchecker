package battleboats_1.com.cyberpointllc.stac.dialogs;

import io.netty.channel.Channel;
import io.netty.util.AttributeKey;

import java.net.InetSocketAddress;

public final class TalkersConnection {

    public static final AttributeKey<TalkersConnection> CONNECTION_ATTR = new AttributeKey<>("CONNECTION_ATTR");

    private final Channel channel;
    private final TalkersPublicEmpty theirEmpty;

    /**
     * @param channel the netty channel to use for comms
     * @param theirEmpty the identity of the other side of this connection
     */
    public TalkersConnection(Channel channel, TalkersPublicEmpty theirEmpty) {
        this.channel = channel;
        this.theirEmpty = theirEmpty;
    }

    /**
     * Sends str to the other side of the connection
     * @param str
     * @throws TalkersDeviation
     */
    public void write(String str) throws TalkersDeviation {
        write(str.getBytes());
    }

    /**
     * Sends bytes to the other side of the connection
     * @param bytes
     * @throws TalkersDeviation
     */
    public void write(byte[] bytes) throws TalkersDeviation {
        channel.writeAndFlush(bytes);
    }

    /**
     * Closes the connection gracefully
     * @throws TalkersDeviation
     */
    public void close() throws TalkersDeviation {
        try {
            channel.close().sync();
        } catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    public boolean isOpen() {
        return channel.isOpen();
    }

    /**
     * @return the identity of the other end of the connection
     */
    public TalkersPublicEmpty grabTheirEmpty() {
        return theirEmpty;
    }

    public String grabRemoteHomeString() {
        InetSocketAddress sa = (InetSocketAddress) channel.remoteAddress();
        return sa.getHostString();
    }

    public int grabRemotePort() {
        InetSocketAddress sa = (InetSocketAddress) channel.remoteAddress();
        return sa.getPort();
    }

    @Override
    // Note: this only compares the identity (not the channel)
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TalkersConnection connection = (TalkersConnection) o;
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
        return grabTheirEmpty().grabId().toString();
    }

}
