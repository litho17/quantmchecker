package gabfeed_1.com.cyberpointllc.stac.gabfeed.model;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import java.util.HashMap;
import gabfeed_1.com.cyberpointllc.stac.template.Templated;
import org.apache.commons.lang3.StringEscapeUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.Comparator;
import java.util.Date;
import java.util.Map;

public class GabMessage implements Templated {

    public static final GabMessageAscendingComparator ASCENDING_COMPARATOR = new  GabMessageAscendingComparator();

    public static final GabMessageDescendingComparator DESCENDING_COMPARATOR = new  GabMessageDescendingComparator();

    private final GabDatabase db;

    private final String id;

    private final String contents;

    private final String authorId;

    private final Date postDate;

    private final boolean publicMessage;

    public GabMessage(GabDatabase db, String id, String contents, String authorId, Date postDate, boolean isPublicMessage) {
        this.db = db;
        this.id = id;
        this.contents = contents;
        this.authorId = authorId;
        this.postDate = postDate;
        this.publicMessage = isPublicMessage;
    }

    public String getContents() {
        return contents;
    }

    public String getAuthorId() {
        return authorId;
    }

    public String getId() {
        return id;
    }

    public Date getPostDate() {
        return postDate;
    }

    public boolean isPublicMessage() {
        return publicMessage;
    }

    @Override
    public @Inv("+<self>=+c63+c64+c65+c66+c72+c73") Map<String, String> getTemplateMap() {
        @Inv("+<self>=+c63+c64+c65+c66+c72+c73") Map<String, String> templateMap = new  HashMap();
        c63: templateMap.put("messageId", id);
        c64: templateMap.put("messageContents", StringEscapeUtils.escapeHtml4(contents));
        c65: templateMap.put("messageAuthorId", authorId);
        c66: templateMap.put("messagePostDate", postDate.toString());
        String displayName = authorId;
        GabUser user = db.getUser(authorId);
        if (user != null) {
            displayName = user.getDisplayName();
        }
        c72: templateMap.put("messageAuthorDisplayName", displayName);
        c73: templateMap.put("publicMessage", Boolean.toString(publicMessage));
        return templateMap;
    }

    public static class GabMessageAscendingComparator implements Comparator<GabMessage> {

        @Override
        public int compare(GabMessage gabMessage1, GabMessage gabMessage2) {
            Date message1Date = gabMessage1.getPostDate();
            Date message2Date = gabMessage2.getPostDate();
            return message1Date.compareTo(message2Date);
        }
    }

    public static class GabMessageDescendingComparator implements Comparator<GabMessage> {

        @Override
        public int compare(GabMessage gabMessage1, GabMessage gabMessage2) {
            Date message1Date = gabMessage1.getPostDate();
            Date message2Date = gabMessage2.getPostDate();
            return message2Date.compareTo(message1Date);
        }
    }
}
