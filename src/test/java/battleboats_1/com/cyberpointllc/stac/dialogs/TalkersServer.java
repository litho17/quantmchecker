package battleboats_1.com.cyberpointllc.stac.dialogs;

import battleboats_1.com.cyberpointllc.stac.dialogs.internal.TalkersChannelInitializer;
import io.netty.bootstrap.ServerBootstrap;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioServerSocketChannel;

/**
 * Waits for connections from a client
 */
public class TalkersServer {

    private int listenPort;
    private final ServerBootstrap bootstrap;
    private final EventLoopGroup serverGroup;

    public TalkersServer(int listenPort, TalkersManager manager, TalkersEmpty empty) {
        this(listenPort, manager, empty, new NioEventLoopGroup(1));
    }

    /**
     * @param listenPort port to listen on
     * @param manager used to notify users of data and connection events
     * @param empty the identiy of the server
     * @param eventLoopGroup
     */
    public TalkersServer(int listenPort, TalkersManager manager, TalkersEmpty empty, EventLoopGroup eventLoopGroup) {
        this.listenPort = listenPort;
        bootstrap = new ServerBootstrap();
        serverGroup = eventLoopGroup;
        bootstrap.group(serverGroup)
                .channel(NioServerSocketChannel.class);
        bootstrap.childHandler(new TalkersChannelInitializer(manager, empty, true));
    }

    /**
     * Starts serving asyncronously
     */
    public void serve() throws TalkersDeviation {
        try {
            bootstrap.bind(listenPort).sync();
        } catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    /**
     * Stops serving
     */
    public void close() {
        serverGroup.shutdownGracefully();
    }

}
