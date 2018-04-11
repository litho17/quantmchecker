package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabMessage;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabRoom;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabThread;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabUser;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import gabfeed_1.com.cyberpointllc.stac.sort.Sorter;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSession;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSessionService;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebTemplate;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.AbstractHttpHandler;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.net.HttpURLConnection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ThreadHandler extends GabHandler {

    private static final String PATH = "/thread/";

    private final WebTemplate threadTemplate;

    private final WebTemplate messageListTemplate;

    private final WebTemplate messageListTemplateWithoutTime;

    public ThreadHandler(GabDatabase db, WebSessionService webSessionService) {
        super(db, webSessionService);
        this.threadTemplate = new  WebTemplate("ThreadTemplate.html", getClass());
        this.messageListTemplate = new  WebTemplate("MessageListSnippet.html", getClass());
        this.messageListTemplateWithoutTime = new  WebTemplate("MessageListSnippetWithoutTime.html", getClass());
    }

    @Override
    public String getPath() {
        return PATH;
    }

    /**
     * @param threadId thread to display
     * @return the path to the thread.
     */
    public static String getPathToThread(String threadId) {
        return PATH + threadId;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange, String threadId, GabUser user) {
        WebSession webSession = getWebSessionService().getSession(httpExchange);
        String query = httpExchange.getRequestURI().getQuery();
        if (!StringUtils.isBlank(query) && query.equals("suppressTimestamp=true")) {
            webSession.setProperty("suppressTimestamp", "true");
        }
        GabThread thread = getDb().getThread(threadId);
        if (thread == null) {
            return AbstractHttpHandler.getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid Room: " + threadId);
        }
        GabRoom room = thread.getRoom();
        @Inv("+<self>=+c66+c67") List<Link> menuItems = new  LinkedList();
        c66: menuItems.add(new  Link(RoomHandler.getPathToRoom(room.getId()), room.getName()));
        c67: menuItems.add(new  Link(NewMessageHandler.getPathToPostToThread(thread.getId()), "New Message"));
        return getTemplateResponse(thread.getName(), getContents(thread, webSession), user, menuItems);
    }

    private String getContents(GabThread thread, WebSession webSession) {
        String suppressTimestampString = webSession.getProperty("suppressTimestamp", "false");
        boolean suppressTimestamp = Boolean.parseBoolean(suppressTimestampString);
        @Inv("+<self>=+c84+c86") StringBuilder builder = new  StringBuilder();
        List<GabMessage> messages = thread.getMessages();
        Sorter sorter = new  Sorter(GabMessage.ASCENDING_COMPARATOR);
        messages = sorter.sort(messages);
        for (GabMessage message : messages) {
            @Inv("+<self>=+c82") Map<String, String> messageMap = message.getTemplateMap();
            // fix up the contents
            String content = messageMap.get("messageContents");
            c82: messageMap.put("messageContents", PageUtils.formatLongString(content, webSession));
            if (!suppressTimestamp) {
                c84: messageListTemplate.getEngine().replaceTagsBuilder(messageMap, builder);
            } else {
                c86: messageListTemplateWithoutTime.getEngine().replaceTagsBuilder(messageMap, builder);
            }
        }
        String messageContents = builder.toString();
        @Inv("+<self>=+c91") Map<String, String> threadMap = thread.getTemplateMap();
        c91: threadMap.put("messages", messageContents);
        return threadTemplate.getEngine().replaceTags(threadMap);
    }
}
