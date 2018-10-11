package withmi_1.edu.networkcusp.protocols;

import withmi_1.edu.networkcusp.protocols.internal.CommunicationsChannelInitializer;
import io.netty.bootstrap.Bootstrap;
import io.netty.channel.Channel;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioSocketChannel;

public class CommunicationsClient {

    private final Bootstrap bootstrap;
    private EventLoopGroup group;
    private final CommunicationsChannelInitializer initializer;

    /**
     * @param communicationsGuide handler that will be called when data is available
     * @param identity the client's identity (what we present to the server)
     */
    public CommunicationsClient(CommunicationsGuide communicationsGuide, CommunicationsIdentity identity) {
        bootstrap = new Bootstrap();
        group = new NioEventLoopGroup(1);
        initializer = new CommunicationsChannelInitializer(communicationsGuide, identity, false);
        bootstrap.group(group)
                .channel(NioSocketChannel.class)
                .handler(initializer);
    }

    /**
     * Connects to a server
     * @param host hostname to connect to
     * @param port the port to connect to
     * @return a CommsConnection to be used to send data
     * @throws CommunicationsFailure
     */
    public CommunicationsConnection connect(String host, int port) throws CommunicationsFailure {
        try {
            Channel channel = bootstrap.connect(host, port).sync().channel();
            initializer.awaitForPermission(10000);
            return channel.attr(CommunicationsConnection.CONNECTION_ATTR).get();
        } catch (Exception e) {
            // NOTE: if we don't catch the generic 'Exception' here then
            // some other sort of exception may wind up stalling us.
            // This is because Netty is doing some strange things.
            // See: https://github.com/netty/netty/issues/2597
            throw new CommunicationsFailure(e);
        }
    }

    /**
     * Connects to a server at the specified address
     * @param addr the address of the server
     * @return the connection that can be used to talk to the server
     * @throws CommunicationsFailure
     */
    public CommunicationsConnection connect(CommunicationsNetworkAddress addr) throws CommunicationsFailure {
        return connect(addr.getHost(), addr.pullPort());
    }

    /**
     * Closes the client gracefully
     */
    public void close() {
        group.shutdownGracefully();
    }

    public EventLoopGroup pullEventLoopGroup() {
        return group;
    }
}
