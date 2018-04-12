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

public class GabRoom implements Templated {

    public static final GabRoomAscendingComparator ASCENDING_COMPARATOR = new  GabRoomAscendingComparator();

    private final GabDatabase db;

    private final String id;

    private final String name;

    private final String description;

    private final List<String> threadIds;

    public GabRoom(GabDatabase db, String id, String name, String description) {
        this(db, id, name, description, new  LinkedList<String>());
    }

    public GabRoom(GabDatabase db, String id, String name, String description, List<String> threadIds) {
        this.db = db;
        this.id = id;
        this.name = name;
        this.description = description;
        this.threadIds = threadIds;
    }

    @Summary({"threadIds", "1"})
    public GabThread addThread(String name, String authorId) {
        String threadId = getId() + "_" + this.threadIds.size();
        GabThread thread = new  GabThread(db, threadId, name, authorId, new  Date());
        threadIds.add(threadId);
        db.addThread(thread);
        db.addRoom(this);
        return thread;
    }

    public String getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getDescription() {
        return description;
    }

    public List<String> getThreadIds() {
        return threadIds;
    }

    public List<GabThread> getThreads() {
        @Inv("+<self>=+c69-c68") LinkedList<GabThread> threads = new  LinkedList();
        c68: for (String threadId : getThreadIds()) {
            c69: threads.add(db.getThread(threadId));
        }
        return threads;
    }

    @Override
    public Map<String, String> getTemplateMap() {
        @Inv("+<self>=+c77+c78+c79") Map<String, String> templateMap = new  HashMap();
        c77: templateMap.put("roomId", id);
        c78: templateMap.put("roomName", StringEscapeUtils.escapeHtml4(name));
        c79: templateMap.put("roomDescription", StringEscapeUtils.escapeHtml4(description));
        return templateMap;
    }

    public static class GabRoomAscendingComparator implements Comparator<GabRoom> {

        @Override
        public int compare(GabRoom gabRoom1, GabRoom gabRoom2) {
            return gabRoom1.id.compareTo(gabRoom2.id);
        }
    }
}
