package withmi_1.edu.networkcusp.protocols;

import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import withmi_1.edu.networkcusp.math.CryptoPrivateKey;
import withmi_1.edu.networkcusp.math.CryptoPublicKey;

import java.io.File;
import java.io.FileReader;

public class CommunicationsIdentity {

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoPrivateKey key;
    private final CommunicationsNetworkAddress callbackAddress;

    public CommunicationsIdentity(String id, CryptoPrivateKey key) {
        this(id, key, null);
    }

    public CommunicationsIdentity(String id, CryptoPrivateKey key, CommunicationsNetworkAddress callbackAddress) {
        this.id = id;
        this.key = key;
        this.callbackAddress = callbackAddress;
    }

    public static CommunicationsIdentity loadFromFile(File identityFile) throws CommunicationsFailure {
        @InvUnk("Unknown API") JSONParser parser = new JSONParser();
        try {
            @InvUnk("Extend library class") JSONObject jackson = (JSONObject) parser.parse(new FileReader(identityFile));
            JSONObject privateKeyJackson = (JSONObject) jackson.get("privateKey");
            CryptoPrivateKey privateKey = CryptoPrivateKey.createKeyFromJackson(privateKeyJackson);
            String id = (String) jackson.get("id");
            String callbackHost = (String) jackson.get("callbackHost");
            long callbackPort = (long) jackson.get("callbackPort");
            return new CommunicationsIdentity(id, privateKey, new CommunicationsNetworkAddress(callbackHost, (int)callbackPort));
        }
        catch (Exception e) {
            throw new CommunicationsFailure(e);
        }
    }

    public String toJackson() {
        @InvUnk("Extend library class") JSONObject jackson = new JSONObject();
        jackson.put("id", id);
        jackson.put("callbackHost", callbackAddress.getHost());
        jackson.put("callbackPort", callbackAddress.pullPort());
        jackson.put("privateKey", key.toJACKSONString());
        return jackson.toJSONString();
    }

    public String obtainId() { return id; }

    public String grabTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoPublicKey takePublicKey() { return key.fetchPublicKey(); }

    public CryptoPrivateKey fetchPrivateKey() { return key; }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    public CommunicationsNetworkAddress pullCallbackAddress() { return callbackAddress; }

    /**
     * @return the public identity associated with this identity (safe to give to anyone)
     */
    public CommunicationsPublicIdentity pullPublicIdentity() {
        return new CommunicationsPublicIdentity(id, takePublicKey(), callbackAddress);
    }

    @Override
    public String toString() {
        return "id: " + id + "\n" + key;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsIdentity identity = (CommunicationsIdentity) o;

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
