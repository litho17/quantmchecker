package battleboats_1.com.cyberpointllc.stac.dialogs.internal;

import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersConnection;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersDeviation;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersManager;
import battleboats_1.com.cyberpointllc.stac.dialogs.TalkersEmpty;
import io.netty.channel.Channel;
import io.netty.channel.ChannelDuplexHandler;
import io.netty.channel.ChannelHandlerContext;
import io.netty.channel.ChannelPromise;
import io.netty.util.concurrent.Promise;


/**
 * Used in the Netty framework to do our auth and crypto
 */
public class TalkersNettyManager extends ChannelDuplexHandler { //extends SimpleChannelInboundHandler<byte[]> {
    private final TalkersManager manager;
    private final TalkersCryptoStage cryptoStage;
    private final boolean isServer;
    private Promise authenticatedPromise;

    /**
     *
     * @param manager the CommsHandler that will be notified when data arrives or connections close or open
     * @param empty the identity of the entity using this handler (i.e. this end of the connection)
     * @param isServer true if this is being used as a server
     * @param authenticatedPromise signaled when we're successfully authenticated
     * @throws TalkersDeviation
     */
    public TalkersNettyManager(TalkersManager manager, TalkersEmpty empty, boolean isServer, Promise authenticatedPromise) throws TalkersDeviation {
        this.manager = manager;
        this.cryptoStage = new TalkersCryptoStage(empty);
        this.isServer = isServer;
        this.authenticatedPromise = authenticatedPromise;
    }

    @Override
    public void channelActive(ChannelHandlerContext ctx) throws Exception {
        super.channelActive(ctx);
        // TCP connection was just established, time to deal with
        // authenication, but client goes first...
        if (!isServer && cryptoStage.hasSetupMessage()) {
            // client is responsible for sending first message
            byte[] setupMsg = cryptoStage.takeFollowingSetupMessage();
            ctx.writeAndFlush(setupMsg);
        }
    }

    @Override
    public void channelInactive(ChannelHandlerContext ctx) throws Exception {
        super.channelInactive(ctx);
        // TCP connection was just closed
        TalkersConnection connection = ctx.channel().attr(TalkersConnection.CONNECTION_ATTR).get();
        // the connection may be null, if we did not successfully connect to the other user
        // if that's the case, we don't need to disconnect from the other user
        if (connection != null) {
            manager.closedConnection(connection);
        }
    }

    @Override
    public void channelRead(ChannelHandlerContext ctx, Object msg) throws Exception {
        if (cryptoStage.isReady()) {
            // If the cryptoState is ready, then this is just regular user data, give it to them
            // after we decrypt it
            byte[] data = cryptoStage.decrypt((byte[]) msg);

            manager.handle(ctx.channel().attr(TalkersConnection.CONNECTION_ATTR).get(), data);
        } else {
            // if it isn't ready, the this should be a setup message, process it as one
            cryptoStage.processFollowingSetupMessage((byte[]) msg);

            // does it have another setup message to send?
            if (cryptoStage.hasSetupMessage()) {
                byte[] followingMsg = cryptoStage.takeFollowingSetupMessage();
                ctx.writeAndFlush(followingMsg);
            }


            // has the RSA authentication test failed?
            if (cryptoStage.hasFailed()) {
                // if it has, close the connection
                ctx.close();
                authenticatedPromise.setFailure(new TalkersDeviation("Failed handshake"));
            }

            // is it ready now (are we all authenticated and everything)?
            if (cryptoStage.isReady()) {
                channelReadCoordinator(ctx);
            }
        }
    }

    private void channelReadCoordinator(ChannelHandlerContext ctx) throws TalkersDeviation {
        Channel ch = ctx.channel();
        TalkersConnection connection = new TalkersConnection(ch, cryptoStage.obtainTheirEmpty());
        ch.attr(TalkersConnection.CONNECTION_ATTR).set(connection);

        // clients will be waiting for this event
        authenticatedPromise.setSuccess(null);

        // the server will want to know about the new connection
        // we don't even notify it until authentication is complete
        if (isServer) {
            manager.newConnection(connection);
        }
    }

    @Override
    public void write(ChannelHandlerContext ctx, Object msg, ChannelPromise promise) throws Exception {
        if (cryptoStage.isReady()) {
            // we can send user data now, we just have to encrypt it first...
            byte[] data = cryptoStage.encrypt((byte[]) msg);
            super.write(ctx, data, promise);
        } else {
            throw new TalkersDeviation("Trying to send data, but cryptostate isn't ready yet!");
        }
    }

    /**
     * Wait for authentication to be completed
     * @param timeoutmillis the amount of time to wait...
     * @throws TalkersDeviation
     */
    public void awaitForPermission(long timeoutmillis) throws TalkersDeviation {
        try {
            authenticatedPromise.await(timeoutmillis);
            if (!authenticatedPromise.isSuccess()) {
                throw new TalkersDeviation(authenticatedPromise.cause().getMessage());
            }
        } catch (InterruptedException e) {
            throw new TalkersDeviation(e);
        }
    }
}
