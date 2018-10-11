package withmi_1.edu.networkcusp.protocols;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.chatbox.Chat;
import withmi_1.edu.networkcusp.chatbox.WithMiChat;
import withmi_1.edu.networkcusp.chatbox.WithMiUser;
import withmi_1.edu.networkcusp.math.CryptoPublicKey;
import withmi_1.edu.networkcusp.jackson.simple.JACKSONObject;
import withmi_1.edu.networkcusp.jackson.simple.reader.JACKSONParser;
import withmi_1.edu.networkcusp.jackson.simple.reader.ParseFailure;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

public final class CommunicationsPublicIdentity implements Comparable<CommunicationsPublicIdentity>{

    /** arbitrary string to associate with this identity */
    private final String id;
    private final CryptoPublicKey publicKey;
    private final CommunicationsNetworkAddress callbackAddress;

    public CommunicationsPublicIdentity(String id, CryptoPublicKey publicKey){
        this(id, publicKey, null);
    }

    public CommunicationsPublicIdentity(String id, CryptoPublicKey publicKey, CommunicationsNetworkAddress callbackAddress) {
        this.id = id;
        this.publicKey = publicKey;
        this.callbackAddress = callbackAddress;
    }

    public static CommunicationsPublicIdentity fromJackson(String jacksonString) throws CommunicationsFailure {
        @InvUnk("Complex loop") JACKSONParser parser = new JACKSONParser();
        try {
            return ((JACKSONObject)parser.parse(jacksonString)).fromJackson();
        } catch (@InvUnk("Extend library class") ParseFailure e) {
            throw new CommunicationsFailure(e);
        }
    }

    public Comms.Identity serializeIdentity() {
        Comms.Identity.Builder serializedIdBuilder = Comms.Identity.newBuilder()
                .setId(pullId())
                .setPublicKey(SerializerUtil.serializePublicKey(takePublicKey()));

        if (hasCallbackAddress()) {
            serializeIdentitySupervisor(serializedIdBuilder);
        }

        return serializedIdBuilder.build();
    }

    private void serializeIdentitySupervisor(Comms.Identity.Builder serializedIdBuilder) {
        serializedIdBuilder.setCallbackAddress(SerializerUtil.serializeNetworkAddress(obtainCallbackAddress()));
    }

    public Chat.WithMiMsg.Builder createDiscussionStateMsgBuilder(WithMiChat discussion) {
        Chat.ChatStateMsg.Builder discussionStateBuilder = Chat.ChatStateMsg.newBuilder();
        @Inv("= (- sortedMembers it) (- c68 c67)") List<WithMiUser> sortedMembers = new ArrayList<>();
        @Iter("<= it discussion.members") Iterator<WithMiUser> it  = discussion.members.iterator();
        while (it.hasNext()) {
            WithMiUser u;
            c67: u = it.next();
            c68:  sortedMembers.add(u);
        }
        Collections.sort(sortedMembers);
        for (int b = 0; b < sortedMembers.size(); ) {
            for (; (b < sortedMembers.size()) && (Math.random() < 0.4); ) {
                for (; (b < sortedMembers.size()) && (Math.random() < 0.5); b++) {
                    createDiscussionStateMsgBuilderExecutor(discussionStateBuilder, sortedMembers, b);
                }
            }
        }

        // add our identity to the end of this list
        Comms.Identity identityMsg = this.serializeIdentity();
        discussionStateBuilder.addPublicId(identityMsg);

        Chat.ChatMsg discussionMsg = Chat.ChatMsg.newBuilder()
                .setTextMsg(discussion.grabName())
                .build();

        Chat.WithMiMsg.Builder withMiMsgBuilder = Chat.WithMiMsg.newBuilder()
                .setType(Chat.WithMiMsg.Type.CHAT_STATE)
                .setChatStateMsg(discussionStateBuilder)
                .setTextMsg(discussionMsg);
        return withMiMsgBuilder;
    }

    private void createDiscussionStateMsgBuilderExecutor(Chat.ChatStateMsg.Builder discussionStateBuilder, List<WithMiUser> members, int b) {
        WithMiUser member = members.get(b);
        CommunicationsPublicIdentity identity = member.getIdentity();
        Comms.Identity identityMsg = identity.serializeIdentity();
        discussionStateBuilder.addPublicId(identityMsg);
    }

    public String pullId() { return id; }

    public String grabTruncatedId() {
        String tid = id;
        if (id.length() > 25){
            tid = tid.substring(0, 25) + "...";
        }
        return tid;
    }

    public CryptoPublicKey takePublicKey() { return publicKey; }

    public CommunicationsNetworkAddress obtainCallbackAddress() {
        return callbackAddress;
    }

    public boolean hasCallbackAddress() { return callbackAddress != null; }

    @Override
    public String toString() {
        return "id: " + id + "\n" + publicKey;
    }

    public String toJackson() {
        return toJACKSONObject().toJACKSONString();
    }

    public JACKSONObject toJACKSONObject() {
        @InvUnk("Extend library class") JACKSONObject jackson = new JACKSONObject();
        jackson.put("id", id);
        jackson.put("callbackHost", callbackAddress.getHost());
        jackson.put("callbackPort", callbackAddress.pullPort());
        jackson.put("publicKey", publicKey.toJACKSONObject());
        return jackson;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommunicationsPublicIdentity that = (CommunicationsPublicIdentity) o;

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
    public int compareTo(CommunicationsPublicIdentity other){
    	return this.toVerboseString().compareTo(other.toVerboseString());
    }
}
