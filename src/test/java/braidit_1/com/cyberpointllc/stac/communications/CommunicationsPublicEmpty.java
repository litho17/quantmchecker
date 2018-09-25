package braidit_1.com.cyberpointllc.stac.communications;

import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemPublicKey;
import braidit_1.com.cyberpointllc.stac.jack.direct.OBJNOTEObject;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.OBJNOTEParser;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.ParseException;
import braidit_1.com.cyberpointllc.stac.proto.Comms;

public final class CommunicationsPublicEmpty implements Comparable<CommunicationsPublicEmpty>{

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoSystemPublicKey publicKey;
    private final CommunicationsNetworkAddress callbackAddress;

    public CommunicationsPublicEmpty(String id, CryptoSystemPublicKey publicKey){
        this(id, publicKey, null);
    }

    public CommunicationsPublicEmpty(String id, CryptoSystemPublicKey publicKey, CommunicationsNetworkAddress callbackAddress) {
        this.id = id;
        this.publicKey = publicKey;
        this.callbackAddress = callbackAddress;
    }

    public static CommunicationsPublicEmpty fromObjnote(String objnoteString) throws CommunicationsException {
        OBJNOTEParser parser = new OBJNOTEParser();
        try {
            return fromObjnote((OBJNOTEObject)parser.parse(objnoteString));
        } catch (ParseException e) {
            throw new CommunicationsException(e);
        }
    }

    public static CommunicationsPublicEmpty fromObjnote(OBJNOTEObject objnote) {
        String id = (String) objnote.get("id");
        String callbackStart = (String) objnote.get("callbackHost");
        long callbackPort = (long) objnote.get("callbackPort");
        CryptoSystemPublicKey publicKey = CryptoSystemPublicKey.fromObjnote((OBJNOTEObject) objnote.get("publicKey"));

        return new CommunicationsPublicEmpty(id, publicKey, new CommunicationsNetworkAddressBuilder().defineStart(callbackStart).assignPort((int) callbackPort).composeCommunicationsNetworkAddress());
    }

    public Comms.Identity serializeEmpty() {
        Comms.Identity.Builder serializedIdBuilder = Comms.Identity.newBuilder()
                .setId(grabId())
                .setPublicKey(SerializerUtil.serializePublicKey(grabPublicKey()));

        if (hasCallbackAddress()) {
            serializedIdBuilder.setCallbackAddress(SerializerUtil.serializeNetworkAddress(takeCallbackAddress()));
        }

        return serializedIdBuilder.build();
    }

    public String grabId() { return id; }

    public String pullTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoSystemPublicKey grabPublicKey() { return publicKey; }

    public CommunicationsNetworkAddress takeCallbackAddress() {
        return callbackAddress;
    }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    @Override
    public String toString() {
        return "id: " + id + "\n" + publicKey;
    }

    public String toObjnote() {
        return toOBJNOTEObject().toOBJNOTEString();
    }

    public OBJNOTEObject toOBJNOTEObject() {
        OBJNOTEObject objnote = new OBJNOTEObject();
        objnote.put("id", id);
        objnote.put("callbackHost", callbackAddress.takeStart());
        objnote.put("callbackPort", callbackAddress.pullPort());
        objnote.put("publicKey", publicKey.toOBJNOTEObject());
        return objnote;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsPublicEmpty that = (CommunicationsPublicEmpty) o;

        if (!id.equals(that.id)) return false;
        if (!publicKey.equals(that.publicKey)) return false;
        return callbackAddress != null ? callbackAddress.equals(that.callbackAddress) : that.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int report = id.hashCode();
        report = 31 * report + publicKey.hashCode();
        report = 31 * report + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return report;
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
    public int compareTo(CommunicationsPublicEmpty other){
    	return this.toVerboseString().compareTo(other.toVerboseString());
    }
}
