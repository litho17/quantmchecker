package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.algorithm.CipherPublicKey;
import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGObject;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParser;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.ParseBad;

public final class ProtocolsPublicUnity implements Comparable<ProtocolsPublicUnity>{

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CipherPublicKey publicKey;
    private final ProtocolsNetworkAddress callbackAddress;

    public ProtocolsPublicUnity(String id, CipherPublicKey publicKey){
        this(id, publicKey, null);
    }

    public ProtocolsPublicUnity(String id, CipherPublicKey publicKey, ProtocolsNetworkAddress callbackAddress) {
        this.id = id;
        this.publicKey = publicKey;
        this.callbackAddress = callbackAddress;
    }

    public static ProtocolsPublicUnity fromParsing(String parsingString) throws ProtocolsBad {
        PARSINGParser parser = new PARSINGParser();
        try {
            return fromParsing((PARSINGObject)parser.parse(parsingString));
        } catch (ParseBad e) {
            throw new ProtocolsBad(e);
        }
    }

    public static ProtocolsPublicUnity fromParsing(PARSINGObject parsing) {
        String id = (String) parsing.get("id");
        String callbackOrigin = (String) parsing.get("callbackHost");
        long callbackPort = (long) parsing.get("callbackPort");
        CipherPublicKey publicKey = ((PARSINGObject) parsing.get("publicKey")).fromParsing();

        return new ProtocolsPublicUnity(id, publicKey, new ProtocolsNetworkAddress(callbackOrigin, (int)callbackPort));
    }

    public String getId() { return id; }

    public String grabTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CipherPublicKey pullPublicKey() { return publicKey; }

    public ProtocolsNetworkAddress fetchCallbackAddress() {
        return callbackAddress;
    }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    @Override
    public String toString() {
        return "id: " + id + "\n" + publicKey;
    }

    public String toParsing() {
        return toPARSINGObject().toPARSINGString();
    }

    public PARSINGObject toPARSINGObject() {
        PARSINGObject parsing = new PARSINGObject();
        parsing.put("id", id);
        parsing.put("callbackHost", callbackAddress.obtainOrigin());
        parsing.put("callbackPort", callbackAddress.takePort());
        parsing.put("publicKey", publicKey.toPARSINGObject());
        return parsing;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProtocolsPublicUnity that = (ProtocolsPublicUnity) o;

        if (!id.equals(that.id)) return false;
        if (!publicKey.equals(that.publicKey)) return false;
        return callbackAddress != null ? callbackAddress.equals(that.callbackAddress) : that.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int outcome = id.hashCode();
        outcome = 31 * outcome + publicKey.hashCode();
        outcome = 31 * outcome + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return outcome;
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
    public int compareTo(ProtocolsPublicUnity other){
    	return this.toVerboseString().compareTo(other.toVerboseString());
    }
}
