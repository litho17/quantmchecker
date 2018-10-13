package simplevote_1.com.cyberpointllc.stac.senderReceivers.internal;

import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsBad;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsGuide;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsUnity;
import io.netty.channel.ChannelInitializer;
import io.netty.channel.socket.SocketChannel;
import io.netty.handler.codec.LengthFieldBasedFrameDecoder;
import io.netty.handler.codec.LengthFieldPrepender;
import io.netty.handler.codec.bytes.ByteArrayDecoder;
import io.netty.handler.codec.bytes.ByteArrayEncoder;

public class ProtocolsChannelInitializer extends ChannelInitializer<SocketChannel> {
    private final ProtocolsGuide guide;
    private final ProtocolsUnity unity;
    private final boolean isServer;
    private ProtocolsNettyGuide nettyGuide;

    public ProtocolsChannelInitializer(ProtocolsGuide guide, ProtocolsUnity unity, boolean isServer) {
        this.guide = guide;
        this.unity = unity;
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
        nettyGuide = new ProtocolsNettyGuide(guide, unity, isServer, ch.newPromise());
        ch.pipeline().addLast(nettyGuide);
    }

    /**
     * Wait for authentication to complete
     *
     * @param timeoutMillis amount of millis to wait for authentication
     * @throws ProtocolsBad if there is trouble waiting for authentication
     */
    public void awaitForAuth(long timeoutMillis) throws ProtocolsBad {
        nettyGuide.awaitForAuth(timeoutMillis);
    }
}
