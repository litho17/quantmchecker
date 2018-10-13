package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.algorithm.CipherPrivateKey;
import simplevote_1.com.cyberpointllc.stac.algorithm.CipherPublicKey;
import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGObject;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParser;

import java.io.File;
import java.io.FileReader;

public class ProtocolsUnity {

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CipherPrivateKey key;
    private final ProtocolsNetworkAddress callbackAddress;

    public ProtocolsUnity(String id, CipherPrivateKey key) {
        this(id, key, null);
    }

    public ProtocolsUnity(String id, CipherPrivateKey key, ProtocolsNetworkAddress callbackAddress) {
        this.id = id;
        this.key = key;
        this.callbackAddress = callbackAddress;
    }

    public static ProtocolsUnity loadFromFile(File unityFile) throws ProtocolsBad {
        PARSINGParser parser = new PARSINGParser();
        try {
            PARSINGObject parsing = (PARSINGObject) parser.parse(new FileReader(unityFile));
            PARSINGObject privateKeyParsing = (PARSINGObject) parsing.get("privateKey");
            CipherPrivateKey privateKey = CipherPrivateKey.formKeyFromParsing(privateKeyParsing);
            String id = (String) parsing.get("id");
            String callbackOrigin = (String) parsing.get("callbackHost");
            long callbackPort = (long) parsing.get("callbackPort");
            return new ProtocolsUnityCreator().defineId(id).defineKey(privateKey).setCallbackAddress(new ProtocolsNetworkAddress(callbackOrigin, (int) callbackPort)).formProtocolsUnity();
        }
        catch (Exception e) {
            throw new ProtocolsBad(e);
        }
    }

    public String toParsing() {
        PARSINGObject parsing = new PARSINGObject();
        parsing.put("id", id);
        parsing.put("callbackHost", callbackAddress.obtainOrigin());
        parsing.put("callbackPort", callbackAddress.takePort());
        parsing.put("privateKey", key.toPARSINGObject());
        return parsing.toPARSINGString();
    }

    public String grabId() { return id; }

    public String grabTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CipherPublicKey getPublicKey() { return key.pullPublicKey(); }

    public CipherPrivateKey grabPrivateKey() { return key; }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    public ProtocolsNetworkAddress pullCallbackAddress() { return callbackAddress; }

    /**
     * @return the public identity associated with this identity (safe to give to anyone)
     */
    public ProtocolsPublicUnity takePublicUnity() {
        return new ProtocolsPublicUnity(id, getPublicKey(), callbackAddress);
    }

    @Override
    public String toString() {
        return "id: " + id + "\n" + key;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProtocolsUnity unity = (ProtocolsUnity) o;

        if (!id.equals(unity.id)) return false;
        if (!key.equals(unity.key)) return false;
        return callbackAddress != null ? callbackAddress.equals(unity.callbackAddress) : unity.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int outcome = id.hashCode();
        outcome = 31 * outcome + key.hashCode();
        outcome = 31 * outcome + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return outcome;
    }
}
