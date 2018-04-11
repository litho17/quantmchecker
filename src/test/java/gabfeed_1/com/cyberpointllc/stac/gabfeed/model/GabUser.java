package gabfeed_1.com.cyberpointllc.stac.gabfeed.model;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import java.util.HashMap;
import gabfeed_1.com.cyberpointllc.stac.template.Templated;
import org.apache.commons.lang3.StringEscapeUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class GabUser implements Templated {

    private final GabDatabase db;

    private final String id;

    private final String displayName;

    private final String password;

    private final List<String> messageIds;

    public GabUser(GabDatabase db, String id, String displayName, String password) {
        this(db, id, displayName, password, new  LinkedList<String>());
    }

    public GabUser(GabDatabase db, String id, String displayName, String password, List<String> messageIds) {
        this.db = db;
        this.id = id;
        this.displayName = displayName;
        this.password = password;
        this.messageIds = messageIds;
    }

    @Summary({"messageIds", "1"})
    public void addMessage(String messageId) {
        messageIds.add(messageId);
        db.addUser(this);
    }

    public String getDisplayName() {
        return displayName;
    }

    public String getId() {
        return id;
    }

    public String getPassword() {
        return password;
    }

    public List<String> getMessageIds() {
        return messageIds;
    }

    public List<GabMessage> getMessages() {
        @Inv("+<self>=+c63-c62") LinkedList<GabMessage> messages = new  LinkedList();
        c62: for (String messageId : getMessageIds()) {
            c63: getMessagesHelper(messageId, messages);
        }
        return messages;
    }

    @Override
    public Map<String, String> getTemplateMap() {
        @Inv("+<self>=+c71+c72") Map<String, String> templateMap = new  HashMap();
        c71: templateMap.put("userId", id);
        c72: templateMap.put("displayName", StringEscapeUtils.escapeHtml4(displayName));
        return templateMap;
    }

    @Summary({"messages", "1"})
    private void getMessagesHelper(String messageId, @Inv("+<self>=+c78") LinkedList<GabMessage> messages) {
        c78: messages.add(db.getMessage(messageId));
    }
}
