package braidit_1.com.cyberpointllc.stac.communications.internal;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsManager;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsEmpty;
import io.netty.channel.ChannelInitializer;
import io.netty.channel.socket.SocketChannel;
import io.netty.handler.codec.LengthFieldBasedFrameDecoder;
import io.netty.handler.codec.LengthFieldPrepender;
import io.netty.handler.codec.bytes.ByteArrayDecoder;
import io.netty.handler.codec.bytes.ByteArrayEncoder;

public class CommunicationsChannelInitializer extends ChannelInitializer<SocketChannel> {
    private final CommunicationsManager manager;
    private final CommunicationsEmpty empty;
    private final boolean isServer;
    private CommunicationsNettyManager nettyManager;

    public CommunicationsChannelInitializer(CommunicationsManager coordinator, CommunicationsEmpty empty, boolean isServer) {
        this.manager = coordinator;
        this.empty = empty;
        this.isServer = isServer;
    }

    @Override
    public void initChannel(SocketChannel ch) throws Exception {
        // using the frame encoder and decoder should make it safe
        // to assume a 'read' will get the entire message...
        ch.pipeline()
                // TODO: allow the user to figure out what the max frame size is...
                .addLast("frameDecoder", new LengthFieldBasedFrameDecoder(1024 * 1024, 0, 4, 0, 4))
                .addLast("frameEncoder", new LengthFieldPrepender(4))
                .addLast("bytesEncoder", new ByteArrayEncoder())
                .addLast("bytesDecoder", new ByteArrayDecoder());

        // this is what does the authentication and encryption
        nettyManager = new CommunicationsNettyManager(manager, empty, isServer, ch.newPromise());
        ch.pipeline().addLast(nettyManager);
    }

    /**
     * Wait for authentication to complete
     *
     * @param timeoutMillis amount of millis to wait for authentication
     * @throws CommunicationsException if there is trouble waiting for authentication
     */
    public void awaitForAuth(long timeoutMillis) throws CommunicationsException {
        nettyManager.awaitForAuth(timeoutMillis);
    }
}
