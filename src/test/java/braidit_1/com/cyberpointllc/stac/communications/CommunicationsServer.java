package braidit_1.com.cyberpointllc.stac.communications;

import braidit_1.com.cyberpointllc.stac.communications.internal.CommunicationsChannelInitializer;
import io.netty.bootstrap.ServerBootstrap;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioServerSocketChannel;

/**
 * Waits for connections from a client
 */
public class CommunicationsServer {

    private int listenPort;
    private final ServerBootstrap bootstrap;
    private final EventLoopGroup serverGroup;

    public CommunicationsServer(int listenPort, CommunicationsManager manager, CommunicationsEmpty empty) {
        this(listenPort, manager, empty, new NioEventLoopGroup(1));
    }

    /**
     * @param listenPort port to listen on
     * @param manager used to notify users of data and connection events
     * @param empty the identiy of the server
     * @param eventLoopGroup
     */
    public CommunicationsServer(int listenPort, CommunicationsManager manager, CommunicationsEmpty empty, EventLoopGroup eventLoopGroup) {
        this.listenPort = listenPort;
        bootstrap = new ServerBootstrap();
        serverGroup = eventLoopGroup;
        bootstrap.group(serverGroup)
                .channel(NioServerSocketChannel.class);
        bootstrap.childHandler(new CommunicationsChannelInitializer(manager, empty, true));
    }

    /**
     * Starts serving asyncronously
     */
    public void serve() throws CommunicationsException {
        try {
            bootstrap.bind(listenPort).sync();
        } catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    /**
     * Stops serving
     */
    public void close() {
        serverGroup.shutdownGracefully();
    }

}
