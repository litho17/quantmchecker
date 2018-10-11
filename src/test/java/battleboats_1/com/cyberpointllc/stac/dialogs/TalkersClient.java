package battleboats_1.com.cyberpointllc.stac.dialogs;

import battleboats_1.com.cyberpointllc.stac.dialogs.internal.TalkersChannelInitializer;
import io.netty.bootstrap.Bootstrap;
import io.netty.channel.Channel;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioSocketChannel;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.util.Objects;

public class TalkersClient {
    private final Bootstrap bootstrap;
    private final EventLoopGroup group;
    private final TalkersChannelInitializer initializer;

    /**
     * @param talkersManager handler that will be called when data is available
     * @param empty     the client's identity (what we present to the server)
     */
    public TalkersClient(TalkersManager talkersManager, TalkersEmpty empty) {
        bootstrap = new Bootstrap();
        group = new NioEventLoopGroup(1);
        initializer = new TalkersChannelInitializer(talkersManager, empty, false);
        bootstrap.group(group)
                .channel(NioSocketChannel.class)
                .handler(initializer);
    }

    /**
     * Connects to a server at the desired host and port pair.
     *
     * @param home hostname to connect to
     * @param port the port to connect to
     * @return CommsConnection to use to send data to the connection
     * @throws TalkersDeviation if there is trouble connecting
     */
    public TalkersConnection connect(String home, int port) throws TalkersDeviation {
        try {
            Channel channel = bootstrap.connect(home, port).sync().channel();
            initializer.awaitForPermission(10000);
            return channel.attr(TalkersConnection.CONNECTION_ATTR).get();
        } catch (@InvUnk("Extend library class") TalkersDeviation e) {
            throw e;
        } catch (Exception e) {
            // NOTE: if we don't catch the generic 'Exception' here then
            // some other sort of exception may wind up stalling us.
            // This is because Netty is doing some strange things.
            // See: https://github.com/netty/netty/issues/2597
            throw new TalkersDeviation(e);
        }
    }

    /**
     * Connects to a server at the specified address.
     *
     * @param addr the address of the server
     * @return the connection that can be used to talk to the server
     * @throws TalkersDeviation       if there is trouble connecting
     * @throws NullPointerException if the addr is <code>null</code>
     */
    public TalkersConnection connect(TalkersNetworkAddress addr) throws TalkersDeviation {
        Objects.requireNonNull(addr, "CommsNetworkAddress may not be null");
        return connect(addr.pullHome(), addr.fetchPort());
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
