package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.senderReceivers.internal.ProtocolsChannelInitializer;
import io.netty.bootstrap.Bootstrap;
import io.netty.channel.Channel;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioSocketChannel;

import java.util.Objects;

public class ProtocolsClient {
    private final Bootstrap bootstrap;
    private final EventLoopGroup group;
    private final ProtocolsChannelInitializer initializer;

    /**
     * @param protocolsGuide handler that will be called when data is available
     * @param unity     the client's identity (what we present to the server)
     */
    public ProtocolsClient(ProtocolsGuide protocolsGuide, ProtocolsUnity unity) {
        bootstrap = new Bootstrap();
        group = new NioEventLoopGroup(1);
        initializer = new ProtocolsChannelInitializer(protocolsGuide, unity, false);
        bootstrap.group(group)
                .channel(NioSocketChannel.class)
                .handler(initializer);
    }

    /**
     * Connects to a server at the desired host and port pair.
     *
     * @param origin hostname to connect to
     * @param port the port to connect to
     * @return CommsConnection to use to send data to the connection
     * @throws ProtocolsBad if there is trouble connecting
     */
    public ProtocolsConnection connect(String origin, int port) throws ProtocolsBad {
        try {
            Channel channel = bootstrap.connect(origin, port).sync().channel();
            initializer.awaitForAuth(10000);
            return channel.attr(ProtocolsConnection.CONNECTION_ATTR).get();
        } catch (ProtocolsBad e) {
            throw e;
        } catch (Exception e) {
            // NOTE: if we don't catch the generic 'Exception' here then
            // some other sort of exception may wind up stalling us.
            // This is because Netty is doing some strange things.
            // See: https://github.com/netty/netty/issues/2597
            throw new ProtocolsBad(e);
        }
    }

    /**
     * Connects to a server at the specified address.
     *
     * @param addr the address of the server
     * @return the connection that can be used to talk to the server
     * @throws ProtocolsBad       if there is trouble connecting
     * @throws NullPointerException if the addr is <code>null</code>
     */
    public ProtocolsConnection connect(ProtocolsNetworkAddress addr) throws ProtocolsBad {
        Objects.requireNonNull(addr, "CommsNetworkAddress may not be null");
        return connect(addr.obtainOrigin(), addr.takePort());
    }

    /**
     * Closes the client gracefully
     */
    public void close() {
        group.shutdownGracefully();
    }

    public EventLoopGroup grabEventLoopGroup() {
        return group;
    }
}
