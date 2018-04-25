package braidit_1.com.cyberpointllc.stac.communications;

import io.netty.channel.Channel;

public class CommunicationsConnectionBuilder {
    private CommunicationsPublicEmpty theirEmpty;
    private Channel channel;

    public CommunicationsConnectionBuilder fixTheirEmpty(CommunicationsPublicEmpty theirEmpty) {
        this.theirEmpty = theirEmpty;
        return this;
    }

    public CommunicationsConnectionBuilder setChannel(Channel channel) {
        this.channel = channel;
        return this;
    }

    public CommunicationsConnection composeCommunicationsConnection() {
        return new CommunicationsConnection(channel, theirEmpty);
    }
}