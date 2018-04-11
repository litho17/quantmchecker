package gabfeed_1.com.cyberpointllc.stac.gabfeed.model;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import java.util.HashMap;
import gabfeed_1.com.cyberpointllc.stac.template.Templated;
import org.apache.commons.lang3.StringEscapeUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.Comparator;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class GabThread implements Templated {

    public static final GabThreadAscendingComparator ASCENDING_COMPARATOR = new  GabThreadAscendingComparator();

    public static final GabThreadDescendingComparator DESCENDING_COMPARATOR = new  GabThreadDescendingComparator();

    private final GabDatabase db;

    private final String id;

    private final String name;

    private final String authorId;

    private final List<String> messageIds;

    private Date lastUpdated;

    public GabThread(GabDatabase db, String id, String name, String authorId, Date lastUpdated) {
        this(db, id, name, authorId, lastUpdated, new  LinkedList<String>());
    }

    public GabThread(GabDatabase db, String id, String name, String authorId, Date lastUpdated, List<String> messageIds) {
        this.db = db;
        this.id = id;
        this.name = name;
        this.authorId = authorId;
        this.lastUpdated = lastUpdated;
        this.messageIds = messageIds;
    }

    @Summary({"messageIds", "1"})
    public GabMessage addMessage(String contents, String authorId) {
        String messageId = getId() + "_" + messageIds.size();
        Date postDate = new  Date();
        GabMessage message = new  GabMessage(db, messageId, contents, authorId, postDate, true);
        lastUpdated = postDate;
        messageIds.add(messageId);
        db.addMessage(message);
        db.addThread(this);
        return message;
    }

    public String getName() {
        return name;
    }

    public String getId() {
        return id;
    }

    public String getAuthorId() {
        return authorId;
    }

    public Date getLastUpdated() {
        return lastUpdated;
    }

    public String getRoomId() {
        // we know that our id is actually <room id>_<thread number>
        return id.substring(0, id.indexOf('_'));
    }

    public GabRoom getRoom() {
        return db.getRoom(getRoomId());
    }

    public List<String> getMessageIds() {
        return messageIds;
    }

    public List<GabMessage> getMessages() {
        @Inv("+<self>=+c89-c88") LinkedList<GabMessage> messages = new  LinkedList();
        c88: for (String messageId : getMessageIds()) {
            c89: getMessagesHelper(messageId, messages);
        }
        return messages;
    }

    @Override
    public Map<String, String> getTemplateMap() {
        @Inv("+<self>=+c98+c99+c100+c101+c107") Map<String, String> templateMap = new  HashMap();
        c98: templateMap.put("threadId", id);
        c99: templateMap.put("threadName", StringEscapeUtils.escapeHtml4(name));
        c100: templateMap.put("threadAuthorId", authorId);
        c101: templateMap.put("threadLastUpdated", lastUpdated.toString());
        String displayName = authorId;
        GabUser user = db.getUser(authorId);
        if (user != null) {
            displayName = user.getDisplayName();
        }
        c107: templateMap.put("threadAuthorDisplayName", displayName);
        return templateMap;
    }

    public static class GabThreadAscendingComparator implements Comparator<GabThread> {

        @Override
        public int compare(GabThread gabThread1, GabThread gabThread2) {
            Date thread1LastUpdate = gabThread1.getLastUpdated();
            Date thread2LastUpdate = gabThread2.getLastUpdated();
            return thread1LastUpdate.compareTo(thread2LastUpdate);
        }
    }

    public static class GabThreadDescendingComparator implements Comparator<GabThread> {

        @Override
        public int compare(GabThread gabThread1, GabThread gabThread2) {
            Date thread1LastUpdate = gabThread1.getLastUpdated();
            Date thread2LastUpdate = gabThread2.getLastUpdated();
            return thread2LastUpdate.compareTo(thread1LastUpdate);
        }
    }

    @Summary({"messages", "1"})
    private void getMessagesHelper(String messageId, @Inv("+<self>=+c133") LinkedList<GabMessage> messages) {
        c133: messages.add(db.getMessage(messageId));
    }
}
