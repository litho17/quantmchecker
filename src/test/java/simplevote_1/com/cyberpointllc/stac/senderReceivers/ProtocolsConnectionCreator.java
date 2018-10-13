package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import io.netty.channel.Channel;

public class ProtocolsConnectionCreator {
    private Channel channel;
    private ProtocolsPublicUnity theirUnity;

    public ProtocolsConnectionCreator setChannel(Channel channel) {
        this.channel = channel;
        return this;
    }

    public ProtocolsConnectionCreator setTheirUnity(ProtocolsPublicUnity theirUnity) {
        this.theirUnity = theirUnity;
        return this;
    }

    public ProtocolsConnection formProtocolsConnection() {
        return new ProtocolsConnection(channel, theirUnity);
    }
}