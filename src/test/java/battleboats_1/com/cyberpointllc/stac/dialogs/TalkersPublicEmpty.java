package battleboats_1.com.cyberpointllc.stac.dialogs;

import battleboats_1.com.cyberpointllc.stac.numerical.CryptoPublicKey;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.PLUGINObject;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.ContainerFactory;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.PLUGINGrabber;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.ParseDeviation;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

public final class TalkersPublicEmpty implements Comparable<TalkersPublicEmpty>{

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoPublicKey publicKey;
    private final TalkersNetworkAddress callbackAddress;

    public TalkersPublicEmpty(String id, CryptoPublicKey publicKey){
        this(id, publicKey, null);
    }

    public TalkersPublicEmpty(String id, CryptoPublicKey publicKey, TalkersNetworkAddress callbackAddress) {
        this.id = id;
        this.publicKey = publicKey;
        this.callbackAddress = callbackAddress;
    }

    public static TalkersPublicEmpty fromPlugin(String pluginString) throws TalkersDeviation {
        PLUGINGrabber grabber = new PLUGINGrabber();
        try {
            return fromPlugin((PLUGINObject) grabber.parse(pluginString, (ContainerFactory)null));
        } catch (@InvUnk("Extend library class") ParseDeviation e) {
            throw new TalkersDeviation(e);
        }
    }

    public static TalkersPublicEmpty fromPlugin(PLUGINObject plugin) {
        String id = (String) plugin.get("id");
        String callbackHome = (String) plugin.get("callbackHost");
        long callbackPort = (long) plugin.get("callbackPort");
        CryptoPublicKey publicKey = ((PLUGINObject) plugin.get("publicKey")).fromPlugin();

        return new TalkersPublicEmpty(id, publicKey, new TalkersNetworkAddress(callbackHome, (int)callbackPort));
    }

    public String grabId() { return id; }

    public String obtainTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoPublicKey obtainPublicKey() { return publicKey; }

    public TalkersNetworkAddress obtainCallbackAddress() {
        return callbackAddress;
    }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    @Override
    public String toString() {
        return "id: " + id + "\n" + publicKey;
    }

    public String toPlugin() {
        return toPLUGINObject().toPLUGINString();
    }

    public PLUGINObject toPLUGINObject() {
        @InvUnk("Extend library class") PLUGINObject plugin = new PLUGINObject();
        plugin.put("id", id);
        plugin.put("callbackHost", callbackAddress.pullHome());
        plugin.put("callbackPort", callbackAddress.fetchPort());
        plugin.put("publicKey", publicKey.toPLUGINObject());
        return plugin;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TalkersPublicEmpty that = (TalkersPublicEmpty) o;

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
    public int compareTo(TalkersPublicEmpty other){
    	return this.toVerboseString().compareTo(other.toVerboseString());
    }
}
