package powerbroker_1.edu.networkcusp.senderReceivers;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import powerbroker_1.edu.networkcusp.direct.PLUGINObject;
import powerbroker_1.edu.networkcusp.direct.reader.ContainerFactory;
import powerbroker_1.edu.networkcusp.direct.reader.PLUGINGrabber;
import powerbroker_1.edu.networkcusp.math.PrivateCommsPrivateKey;
import powerbroker_1.edu.networkcusp.math.PrivateCommsPublicKey;


import java.io.File;
import java.io.FileReader;

public class ProtocolsIdentity {

    /** arbitrary string to associate with this identity */
    private final String id;
    private final PrivateCommsPrivateKey key;
    private final ProtocolsNetworkAddress callbackAddress;

    public ProtocolsIdentity(String id, PrivateCommsPrivateKey key) {
        this(id, key, null);
    }

    public ProtocolsIdentity(String id, PrivateCommsPrivateKey key, ProtocolsNetworkAddress callbackAddress) {
        this.id = id;
        this.key = key;
        this.callbackAddress = callbackAddress;
    }

    public static ProtocolsIdentity loadFromFile(File identityFile) throws ProtocolsRaiser {
        PLUGINGrabber parser = new PLUGINGrabber();
        try {
            @InvUnk("Complex loop") PLUGINObject jack = (PLUGINObject) parser.parse(new FileReader(identityFile), (ContainerFactory) null);
            PrivateCommsPrivateKey privateKey = PrivateCommsPrivateKey.formKeyFromJack((PLUGINObject) jack.get("privateKey"));
            String id = (String) jack.get("id");
            String callbackPlace = (String) jack.get("callbackHost");
            long callbackPort = (long) jack.get("callbackPort");
            return new ProtocolsIdentity(id, privateKey, new ProtocolsNetworkAddressBuilder().setPlace(callbackPlace).definePort((int) callbackPort).formProtocolsNetworkAddress());
        }
        catch (Exception e) {
            throw new ProtocolsRaiser(e);
        }
    }

    public String pullId() { return id; }

    public String obtainTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public PrivateCommsPublicKey grabPublicKey() { return key.takePublicKey(); }

    public PrivateCommsPrivateKey obtainPrivateKey() { return key; }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    public ProtocolsNetworkAddress getCallbackAddress() { return callbackAddress; }

    /**
     * @return the public identity associated with this identity (safe to give to anyone)
     */
    public ProtocolsPublicIdentity fetchPublicIdentity() {
        return new ProtocolsPublicIdentity(id, grabPublicKey(), callbackAddress);
    }

    @Override
    public String toString() {
        return "id: " + id + "\n" + key;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProtocolsIdentity identity = (ProtocolsIdentity) o;

        if (!id.equals(identity.id)) return false;
        if (!key.equals(identity.key)) return false;
        return callbackAddress != null ? callbackAddress.equals(identity.callbackAddress) : identity.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int result = id.hashCode();
        result = 31 * result + key.hashCode();
        result = 31 * result + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return result;
    }
}
