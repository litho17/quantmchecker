package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.senderReceivers.internal.ProtocolsChannelInitializer;
import io.netty.bootstrap.ServerBootstrap;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.channel.socket.nio.NioServerSocketChannel;

/**
 * Waits for connections from a client
 */
public class ProtocolsServer {

    private int listenPort;
    private final ServerBootstrap bootstrap;
    private final EventLoopGroup serverGroup;

    public ProtocolsServer(int listenPort, ProtocolsGuide guide, ProtocolsUnity unity) {
        this(listenPort, guide, unity, new NioEventLoopGroup(1));
    }

    /**
     * @param listenPort port to listen on
     * @param guide used to notify users of data and connection events
     * @param unity the identiy of the server
     * @param eventLoopGroup
     */
    public ProtocolsServer(int listenPort, ProtocolsGuide guide, ProtocolsUnity unity, EventLoopGroup eventLoopGroup) {
        this.listenPort = listenPort;
        bootstrap = new ServerBootstrap();
        serverGroup = eventLoopGroup;
        bootstrap.group(serverGroup)
                .channel(NioServerSocketChannel.class);
        bootstrap.childHandler(new ProtocolsChannelInitializer(guide, unity, true));
    }

    /**
     * Starts serving asyncronously
     */
    public void serve() throws ProtocolsBad {
        try {
            bootstrap.bind(listenPort).sync();
        } catch (Exception e) {
            throw new ProtocolsBad(e);
        }
    }

    /**
     * Stops serving
     */
    public void close() {
        serverGroup.shutdownGracefully();
    }

}
