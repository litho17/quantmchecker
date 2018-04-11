package battleboats_1.com.cyberpointllc.stac.dialogs.internal;

import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersManager;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersEmpty;
import io.netty.channel.ChannelInitializer;
import io.netty.channel.socket.SocketChannel;
import io.netty.handler.codec.LengthFieldBasedFrameDecoder;
import io.netty.handler.codec.LengthFieldPrepender;
import io.netty.handler.codec.bytes.ByteArrayDecoder;
import io.netty.handler.codec.bytes.ByteArrayEncoder;

public class TalkersChannelInitializer extends ChannelInitializer<SocketChannel> {
    private final TalkersManager manager;
    private final TalkersEmpty empty;
    private final boolean isServer;
    private TalkersNettyManager nettyManager;

    public TalkersChannelInitializer(TalkersManager manager, TalkersEmpty empty, boolean isServer) {
        this.manager = manager;
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
        nettyManager = new TalkersNettyManager(manager, empty, isServer, ch.newPromise());
        ch.pipeline().addLast(nettyManager);
    }

    /**
     * Wait for authentication to complete
     *
     * @param timeoutMillis amount of millis to wait for authentication
     * @throws TalkersDeviation if there is trouble waiting for authentication
     */
    public void awaitForPermission(long timeoutMillis) throws TalkersDeviation {
        nettyManager.awaitForPermission(timeoutMillis);
    }
}
