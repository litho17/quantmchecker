package braidit_1.com.cyberpointllc.stac.communications.internal;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsConnection;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsConnectionBuilder;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsManager;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsEmpty;
import io.netty.channel.Channel;
import io.netty.channel.ChannelDuplexHandler;
import io.netty.channel.ChannelHandlerContext;
import io.netty.channel.ChannelPromise;
import io.netty.util.concurrent.Promise;


/**
 * Used in the Netty framework to do our auth and crypto
 */
public class CommunicationsNettyManager extends ChannelDuplexHandler { //extends SimpleChannelInboundHandler<byte[]> {
    private final CommunicationsManager manager;
    private final CommunicationsCryptoPhase cryptoPhase;
    private final boolean isServer;
    private Promise authenticatedPromise;

    /**
     *
     * @param coordinator the CommsHandler that will be notified when data arrives or connections close or open
     * @param empty the identity of the entity using this handler (i.e. this end of the connection)
     * @param isServer true if this is being used as a server
     * @param authenticatedPromise signaled when we're successfully authenticated
     * @throws CommunicationsException
     */
    public CommunicationsNettyManager(CommunicationsManager coordinator, CommunicationsEmpty empty, boolean isServer, Promise authenticatedPromise) throws CommunicationsException {
        this.manager = coordinator;
        this.cryptoPhase = new CommunicationsCryptoPhase(empty);
        this.isServer = isServer;
        this.authenticatedPromise = authenticatedPromise;
    }

    @Override
    public void channelActive(ChannelHandlerContext ctx) throws Exception {
        super.channelActive(ctx);
        // TCP connection was just established, time to deal with
        // authenication, but client goes first...
        if (!isServer && cryptoPhase.hasSetupMessage()) {
            // client is responsible for sending first message
            byte[] setupMsg = cryptoPhase.getEnsuingSetupMessage();
            ctx.writeAndFlush(setupMsg);
        }
    }

    @Override
    public void channelInactive(ChannelHandlerContext ctx) throws Exception {
        super.channelInactive(ctx);
        // TCP connection was just closed
        CommunicationsConnection connection = ctx.channel().attr(CommunicationsConnection.CONNECTION_ATTR).get();
        // the connection may be null, if we did not successfully connect to the other user
        // if that's the case, we don't need to disconnect from the other user
        if (connection != null) {
            manager.closedConnection(connection);
        }
    }

    @Override
    public void channelRead(ChannelHandlerContext ctx, Object msg) throws Exception {
        if (cryptoPhase.isReady()) {
            // If the cryptoState is ready, then this is just regular user data, give it to them
            // after we decrypt it
            byte[] data = cryptoPhase.decrypt((byte[]) msg);

            manager.handle(ctx.channel().attr(CommunicationsConnection.CONNECTION_ATTR).get(), data);
        } else {
            // if it isn't ready, the this should be a setup message, process it as one
            cryptoPhase.processEnsuingSetupMessage((byte[]) msg);

            // does it have another setup message to send?
            if (cryptoPhase.hasSetupMessage()) {
                byte[] ensuingMsg = cryptoPhase.getEnsuingSetupMessage();
                ctx.writeAndFlush(ensuingMsg);
            }


            // has the RSA authentication test failed?
            if (cryptoPhase.hasFailed()) {
                // if it has, close the connection
                ctx.close();
                authenticatedPromise.setFailure(new CommunicationsException("Failed handshake"));
            }

            // is it ready now (are we all authenticated and everything)?
            if (cryptoPhase.isReady()) {
                Channel ch = ctx.channel();
                CommunicationsConnection connection = new CommunicationsConnectionBuilder().setChannel(ch).fixTheirEmpty(cryptoPhase.pullTheirEmpty()).composeCommunicationsConnection();
                ch.attr(CommunicationsConnection.CONNECTION_ATTR).set(connection);

                // clients will be waiting for this event
                authenticatedPromise.setSuccess(null);

                // the server will want to know about the new connection
                // we don't even notify it until authentication is complete
                if (isServer) {
                    manager.newConnection(connection);
                }
            }
        }
    }

    @Override
    public void write(ChannelHandlerContext ctx, Object msg, ChannelPromise promise) throws Exception {
        if (cryptoPhase.isReady()) {
            // we can send user data now, we just have to encrypt it first...
            byte[] data = cryptoPhase.encrypt((byte[]) msg);
            super.write(ctx, data, promise);
        } else {
            throw new CommunicationsException("Trying to send data, but cryptostate isn't ready yet!");
        }
    }

    /**
     * Wait for authentication to be completed
     * @param timeoutmillis the amount of time to wait...
     * @throws CommunicationsException
     */
    public void awaitForAuth(long timeoutmillis) throws CommunicationsException {
        try {
            authenticatedPromise.await(timeoutmillis);
            if (!authenticatedPromise.isSuccess()) {
                throw new CommunicationsException(authenticatedPromise.cause().getMessage());
            }
        } catch (InterruptedException e) {
            throw new CommunicationsException(e);
        }
    }
}
