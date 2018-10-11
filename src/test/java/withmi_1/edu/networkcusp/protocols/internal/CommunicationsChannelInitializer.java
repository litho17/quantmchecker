package withmi_1.edu.networkcusp.protocols.internal;

import withmi_1.edu.networkcusp.protocols.CommunicationsFailure;
import withmi_1.edu.networkcusp.protocols.CommunicationsGuide;
import withmi_1.edu.networkcusp.protocols.CommunicationsIdentity;
import io.netty.channel.ChannelInitializer;
import io.netty.channel.socket.SocketChannel;
import io.netty.handler.codec.LengthFieldBasedFrameDecoder;
import io.netty.handler.codec.LengthFieldPrepender;
import io.netty.handler.codec.bytes.ByteArrayDecoder;
import io.netty.handler.codec.bytes.ByteArrayEncoder;

/**
 * Created by thennen on 2/5/16.
 */
public class CommunicationsChannelInitializer extends ChannelInitializer<SocketChannel> {

    private final CommunicationsGuide guide;
    private final CommunicationsIdentity identity;
    private final boolean isServer;
    private CommunicationsNettyGuide nettyGuide;

    public CommunicationsChannelInitializer(CommunicationsGuide guide, CommunicationsIdentity identity, boolean isServer) {
        this.guide = guide;
        this.identity = identity;
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
        nettyGuide = new CommunicationsNettyGuide(guide, identity, isServer, ch.newPromise());
        ch.pipeline().addLast(nettyGuide);
    }

    /**
     * Wait for authentication to complete
     * @param timeoutMillis amount of millis to wait for authentication
     * @throws CommunicationsFailure
     */
    public void awaitForPermission(long timeoutMillis) throws CommunicationsFailure {
        nettyGuide.awaitForPermission(timeoutMillis);
    }
}
