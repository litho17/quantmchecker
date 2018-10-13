package powerbroker_1.edu.networkcusp.senderReceivers;

import org.json.simple.JSONObject;
import powerbroker_1.edu.networkcusp.math.PrivateCommsPublicKey;

public final class ProtocolsPublicIdentity implements Comparable<ProtocolsPublicIdentity>{

    /** arbitrary string to associate with this identity */
    private final String id;
    private final PrivateCommsPublicKey publicKey;
    private final ProtocolsNetworkAddress callbackAddress;

    public ProtocolsPublicIdentity(String id, PrivateCommsPublicKey publicKey){
        this(id, publicKey, null);
    }

    public ProtocolsPublicIdentity(String id, PrivateCommsPublicKey publicKey, ProtocolsNetworkAddress callbackAddress) {
        this.id = id;
        this.publicKey = publicKey;
        this.callbackAddress = callbackAddress;
    }

    public static ProtocolsPublicIdentity fromJack(JSONObject jack) {
        String id = (String) jack.get("id");
        String callbackPlace = (String) jack.get("callbackHost");
        long callbackPort = (long) jack.get("callbackPort");
        PrivateCommsPublicKey publicKey = PrivateCommsPublicKey.fromJack((JSONObject) jack.get("publicKey"));

        return new ProtocolsPublicIdentity(id, publicKey, new ProtocolsNetworkAddressBuilder().setPlace(callbackPlace).definePort((int) callbackPort).formProtocolsNetworkAddress());
    }

    public String fetchId() { return id; }

    public String obtainTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public PrivateCommsPublicKey takePublicKey() { return publicKey; }

    public ProtocolsNetworkAddress takeCallbackAddress() {
        return callbackAddress;
    }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    @Override
    public String toString() {
        return "id: " + id + "\n" + publicKey;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProtocolsPublicIdentity that = (ProtocolsPublicIdentity) o;

        if (!id.equals(that.id)) return false;
        if (!publicKey.equals(that.publicKey)) return false;
        return callbackAddress != null ? callbackAddress.equals(that.callbackAddress) : that.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int result = id.hashCode();
        result = 31 * result + publicKey.hashCode();
        result = 31 * result + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return result;
    }   
    
    public String toVerboseString(){
    	String str = id + ":" + publicKey.toString() + ": ";
    	if (callbackAddress!=null){
    		str += callbackAddress;
    	} else{
    		str += "NO_CALLBACK";
    	}
    	return str;
    }
    
    @Override
    public int compareTo(ProtocolsPublicIdentity other){
    	return this.toVerboseString().compareTo(other.toVerboseString());
    }
}
