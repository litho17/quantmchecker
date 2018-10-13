package simplevote_1.com.cyberpointllc.stac.senderReceivers.internal;

import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsConnection;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsBad;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsConnectionCreator;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsGuide;
import simplevote_1.com.cyberpointllc.stac.senderReceivers.ProtocolsUnity;
import io.netty.channel.Channel;
import io.netty.channel.ChannelDuplexHandler;
import io.netty.channel.ChannelHandlerContext;
import io.netty.channel.ChannelPromise;
import io.netty.util.concurrent.Promise;


/**
 * Used in the Netty framework to do our auth and crypto
 */
public class ProtocolsNettyGuide extends ChannelDuplexHandler { //extends SimpleChannelInboundHandler<byte[]> {
    private final ProtocolsGuide guide;
    private final ProtocolsCryptoStage cryptoStage;
    private final boolean isServer;
    private Promise authenticatedPromise;

    /**
     *
     * @param guide the CommsHandler that will be notified when data arrives or connections close or open
     * @param unity the identity of the entity using this handler (i.e. this end of the connection)
     * @param isServer true if this is being used as a server
     * @param authenticatedPromise signaled when we're successfully authenticated
     * @throws ProtocolsBad
     */
    public ProtocolsNettyGuide(ProtocolsGuide guide, ProtocolsUnity unity, boolean isServer, Promise authenticatedPromise) throws ProtocolsBad {
        this.guide = guide;
        this.cryptoStage = new ProtocolsCryptoStage(unity);
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
            byte[] setupMsg = cryptoStage.grabNextSetupMessage();
            ctx.writeAndFlush(setupMsg);
        }
    }

    @Override
    public void channelInactive(ChannelHandlerContext ctx) throws Exception {
        super.channelInactive(ctx);
        // TCP connection was just closed
        ProtocolsConnection connection = ctx.channel().attr(ProtocolsConnection.CONNECTION_ATTR).get();
        // the connection may be null, if we did not successfully connect to the other user
        // if that's the case, we don't need to disconnect from the other user
        if (connection != null) {
            guide.closedConnection(connection);
        }
    }

    @Override
    public void channelRead(ChannelHandlerContext ctx, Object msg) throws Exception {
        if (cryptoStage.isReady()) {
            // If the cryptoState is ready, then this is just regular user data, give it to them
            // after we decrypt it
            byte[] data = cryptoStage.decrypt((byte[]) msg);

            guide.handle(ctx.channel().attr(ProtocolsConnection.CONNECTION_ATTR).get(), data);
        } else {
            // if it isn't ready, the this should be a setup message, process it as one
            cryptoStage.processNextSetupMessage((byte[]) msg);

            // does it have another setup message to send?
            if (cryptoStage.hasSetupMessage()) {
                byte[] nextMsg = cryptoStage.grabNextSetupMessage();
                ctx.writeAndFlush(nextMsg);
            }


            // has the RSA authentication test failed?
            if (cryptoStage.hasFailed()) {
                // if it has, close the connection
                ctx.close();
                authenticatedPromise.setFailure(new ProtocolsBad("Failed handshake"));
            }

            // is it ready now (are we all authenticated and everything)?
            if (cryptoStage.isReady()) {
                Channel ch = ctx.channel();
                ProtocolsConnection connection = new ProtocolsConnectionCreator().setChannel(ch).setTheirUnity(cryptoStage.pullTheirUnity()).formProtocolsConnection();
                ch.attr(ProtocolsConnection.CONNECTION_ATTR).set(connection);

                // clients will be waiting for this event
                authenticatedPromise.setSuccess(null);

                // the server will want to know about the new connection
                // we don't even notify it until authentication is complete
                if (isServer) {
                    guide.newConnection(connection);
                }
            }
        }
    }

    @Override
    public void write(ChannelHandlerContext ctx, Object msg, ChannelPromise promise) throws Exception {
        if (cryptoStage.isReady()) {
            // we can send user data now, we just have to encrypt it first...
            byte[] data = cryptoStage.encrypt((byte[]) msg);
            super.write(ctx, data, promise);
        } else {
            throw new ProtocolsBad("Trying to send data, but cryptostate isn't ready yet!");
        }
    }

    /**
     * Wait for authentication to be completed
     * @param timeoutmillis the amount of time to wait...
     * @throws ProtocolsBad
     */
    public void awaitForAuth(long timeoutmillis) throws ProtocolsBad {
        try {
            authenticatedPromise.await(timeoutmillis);
            if (!authenticatedPromise.isSuccess()) {
                throw new ProtocolsBad(authenticatedPromise.cause().getMessage());
            }
        } catch (InterruptedException e) {
            throw new ProtocolsBad(e);
        }
    }
}
