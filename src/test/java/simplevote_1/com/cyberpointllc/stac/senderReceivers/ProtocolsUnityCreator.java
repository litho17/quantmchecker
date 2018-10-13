package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.algorithm.CipherPrivateKey;

public class ProtocolsUnityCreator {
    private String id;
    private CipherPrivateKey key;
    private ProtocolsNetworkAddress callbackAddress = null;

    public ProtocolsUnityCreator defineId(String id) {
        this.id = id;
        return this;
    }

    public ProtocolsUnityCreator defineKey(CipherPrivateKey key) {
        this.key = key;
        return this;
    }

    public ProtocolsUnityCreator setCallbackAddress(ProtocolsNetworkAddress callbackAddress) {
        this.callbackAddress = callbackAddress;
        return this;
    }

    public ProtocolsUnity formProtocolsUnity() {
        return new ProtocolsUnity(id, key, callbackAddress);
    }
}