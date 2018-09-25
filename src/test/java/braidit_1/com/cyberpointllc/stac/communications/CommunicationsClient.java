package braidit_1.com.cyberpointllc.stac.communications;

import braidit_1.com.cyberpointllc.stac.communications.internal.CommunicationsChannelInitializer;
import io.netty.bootstrap.Bootstrap;
import io.netty.channel.Channel;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioSocketChannel;

import java.util.Objects;

public class CommunicationsClient {
    private final Bootstrap bootstrap;
    private final EventLoopGroup group;
    private final CommunicationsChannelInitializer initializer;

    /**
     * @param communicationsManager handler that will be called when data is available
     * @param empty     the client's identity (what we present to the server)
     */
    public CommunicationsClient(CommunicationsManager communicationsManager, CommunicationsEmpty empty) {
        bootstrap = new Bootstrap();
        group = new NioEventLoopGroup(1);
        initializer = new CommunicationsChannelInitializer(communicationsManager, empty, false);
        bootstrap.group(group)
                .channel(NioSocketChannel.class)
                .handler(initializer);
    }

    /**
     * Connects to a server at the desired host and port pair.
     *
     * @param start hostname to connect to
     * @param port the port to connect to
     * @return CommsConnection to use to send data to the connection
     * @throws CommunicationsException if there is trouble connecting
     */
    public CommunicationsConnection connect(String start, int port) throws CommunicationsException {
        try {
            Channel channel = bootstrap.connect(start, port).sync().channel();
            initializer.awaitForAuth(10000);
            return channel.attr(CommunicationsConnection.CONNECTION_ATTR).get();
        } catch (CommunicationsException e) {
            throw e;
        } catch (Exception e) {
            // NOTE: if we don't catch the generic 'Exception' here then
            // some other sort of exception may wind up stalling us.
            // This is because Netty is doing some strange things.
            // See: https://github.com/netty/netty/issues/2597
            throw new CommunicationsException(e);
        }
    }

    /**
     * Connects to a server at the specified address.
     *
     * @param addr the address of the server
     * @return the connection that can be used to talk to the server
     * @throws CommunicationsException       if there is trouble connecting
     * @throws NullPointerException if the addr is <code>null</code>
     */
    public CommunicationsConnection connect(CommunicationsNetworkAddress addr) throws CommunicationsException {
        Objects.requireNonNull(addr, "CommsNetworkAddress may not be null");
        return connect(addr.takeStart(), addr.pullPort());
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
