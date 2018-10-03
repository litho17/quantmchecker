package braidit_1.com.cyberpointllc.stac.communications;

import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemPrivateKey;
import braidit_1.com.cyberpointllc.stac.mathematic.CryptoSystemPublicKey;
import braidit_1.com.cyberpointllc.stac.jack.direct.OBJNOTEObject;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.OBJNOTEParser;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.File;
import java.io.FileReader;

public class CommunicationsEmpty {

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoSystemPrivateKey key;
    private final CommunicationsNetworkAddress callbackAddress;

    public CommunicationsEmpty(String id, CryptoSystemPrivateKey key) {
        this(id, key, null);
    }

    public CommunicationsEmpty(String id, CryptoSystemPrivateKey key, CommunicationsNetworkAddress callbackAddress) {
        this.id = id;
        this.key = key;
        this.callbackAddress = callbackAddress;
    }

    public static CommunicationsEmpty loadFromFile(File emptyFile) throws CommunicationsException {
        @InvUnk("Extend library class") OBJNOTEParser parser = new OBJNOTEParser();
        try {
            OBJNOTEObject objnote = (OBJNOTEObject) parser.parse(new FileReader(emptyFile));
            OBJNOTEObject privateKeyObjnote = (OBJNOTEObject) objnote.get("privateKey");
            CryptoSystemPrivateKey privateKey = CryptoSystemPrivateKey.composeKeyFromObjnote(privateKeyObjnote);
            String id = (String) objnote.get("id");
            String callbackStart = (String) objnote.get("callbackHost");
            long callbackPort = (long) objnote.get("callbackPort");
            return new CommunicationsEmpty(id, privateKey, new CommunicationsNetworkAddressBuilder().defineStart(callbackStart).assignPort((int) callbackPort).composeCommunicationsNetworkAddress());
        }
        catch (Exception e) {
            throw new CommunicationsException(e);
        }
    }

    public String toObjnote() {
        @InvUnk("Extend library class") OBJNOTEObject objnote = new OBJNOTEObject();
        objnote.put("id", id);
        objnote.put("callbackHost", callbackAddress.takeStart());
        objnote.put("callbackPort", callbackAddress.pullPort());
        objnote.put("privateKey", key.toOBJNOTEObject());
        return objnote.toOBJNOTEString();
    }

    public String fetchId() { return id; }

    public String obtainTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoSystemPublicKey getPublicKey() { return key.getPublicKey(); }

    public CryptoSystemPrivateKey fetchPrivateKey() { return key; }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    public CommunicationsNetworkAddress takeCallbackAddress() { return callbackAddress; }

    /**
     * @return the public identity associated with this identity (safe to give to anyone)
     */
    public CommunicationsPublicEmpty grabPublicEmpty() {
        return new CommunicationsPublicEmpty(id, getPublicKey(), callbackAddress);
    }

    @Override
    public String toString() {
        return "id: " + id + "\n" + key;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsEmpty empty = (CommunicationsEmpty) o;

        if (!id.equals(empty.id)) return false;
        if (!key.equals(empty.key)) return false;
        return callbackAddress != null ? callbackAddress.equals(empty.callbackAddress) : empty.callbackAddress == null;

    }

    @Override
    public int hashCode() {
        int report = id.hashCode();
        report = 31 * report + key.hashCode();
        report = 31 * report + (callbackAddress != null ? callbackAddress.hashCode() : 0);
        return report;
    }
}
