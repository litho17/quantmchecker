package battleboats_1.com.cyberpointllc.stac.dialogs;

import battleboats_1.com.cyberpointllc.stac.numerical.CryptoPrivateKey;
import battleboats_1.com.cyberpointllc.stac.numerical.CryptoPublicKey;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.PLUGINObject;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.ContainerFactory;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.PLUGINGrabber;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.File;
import java.io.FileReader;

public class TalkersEmpty {

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoPrivateKey key;
    private final TalkersNetworkAddress callbackAddress;

    public TalkersEmpty(String id, CryptoPrivateKey key) {
        this(id, key, null);
    }

    public TalkersEmpty(String id, CryptoPrivateKey key, TalkersNetworkAddress callbackAddress) {
        this.id = id;
        this.key = key;
        this.callbackAddress = callbackAddress;
    }

    public static TalkersEmpty loadFromFile(File emptyFile) throws TalkersDeviation {
        PLUGINGrabber grabber = new PLUGINGrabber();
        try {
            @InvUnk("Complex loop") PLUGINObject plugin = (PLUGINObject) grabber.parse(new FileReader(emptyFile), (ContainerFactory)null);
            CryptoPrivateKey privateKey = CryptoPrivateKey.makeKeyFromPlugin((PLUGINObject) plugin.get("privateKey"));
            String id = (String) plugin.get("id");
            String callbackHome = (String) plugin.get("callbackHost");
            long callbackPort = (long) plugin.get("callbackPort");
            return new TalkersEmpty(id, privateKey, new TalkersNetworkAddress(callbackHome, (int)callbackPort));
        }
        catch (Exception e) {
            throw new TalkersDeviation(e);
        }
    }

    public String toPlugin() {
        @InvUnk("Extend library class") PLUGINObject plugin = new PLUGINObject();
        plugin.put("id", id);
        plugin.put("callbackHost", callbackAddress.pullHome());
        plugin.put("callbackPort", callbackAddress.fetchPort());
        plugin.put("privateKey", key.toPLUGINObject());
        return plugin.toPLUGINString();
    }

    public String takeId() { return id; }

    public String fetchTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoPublicKey pullPublicKey() { return key.getPublicKey(); }

    public CryptoPrivateKey obtainPrivateKey() { return key; }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    public TalkersNetworkAddress obtainCallbackAddress() { return callbackAddress; }

    /**
     * @return the public identity associated with this identity (safe to give to anyone)
     */
    public TalkersPublicEmpty takePublicEmpty() {
        return new TalkersPublicEmpty(id, pullPublicKey(), callbackAddress);
    }

    @Override
    public String toString() {
        return "id: " + id + "\n" + key;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TalkersEmpty empty = (TalkersEmpty) o;

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
