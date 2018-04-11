package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabChat;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabMessage;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabUser;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import gabfeed_1.com.cyberpointllc.stac.sort.Sorter;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSession;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSessionService;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebTemplate;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.net.HttpURLConnection;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

public class UserHandler extends GabHandler {

    private static final String PATH = "/user/";

    private final WebTemplate userTemplate;

    private final WebTemplate messageListTemplate;

    private final WebTemplate messageListTemplateWithoutTime;

    private final WebTemplate menuTemplate;

    public UserHandler(GabDatabase db, WebSessionService webSessionService) {
        super(db, webSessionService);
        this.userTemplate = new  WebTemplate("UserTemplate.html", getClass());
        this.messageListTemplate = new  WebTemplate("MessageListSnippet.html", getClass());
        this.messageListTemplateWithoutTime = new  WebTemplate("MessageListSnippetWithoutTime.html", getClass());
        this.menuTemplate = new  WebTemplate("MenuItemTemplate.html", getClass());
    }

    @Override
    public String getPath() {
        return PATH;
    }

    /**
     * @param userId user to display
     * @return the path to the thread.
     */
    public static String getPathToUser(String userId) {
        return PATH + userId;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange, String userId, GabUser user) {
        WebSession webSession = getWebSessionService().getSession(httpExchange);
        String query = httpExchange.getRequestURI().getQuery();
        if (!StringUtils.isBlank(query) && query.equals("suppressMessagePostDate=true")) {
            webSession.setProperty("suppressTimestamp", "true");
        }
        GabUser requestedUser = getDb().getUser(userId);
        if (requestedUser == null) {
            return getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid User: " + userId);
        }
        return getTemplateResponse(requestedUser.getDisplayName(), getContents(requestedUser, webSession), user);
    }

    private String getContents(GabUser user, WebSession webSession) {
        String suppressTimestampString = webSession.getProperty("suppressTimestamp", "false");
        boolean suppressTimestamp = Boolean.parseBoolean(suppressTimestampString);
        // TODO:
        // eventually we should do our own thing here
        // like just have a snippet of the content
        // and have a link to the original thread/post
        @Inv("+<self>=+c87+c89") StringBuilder builder = new  StringBuilder();
        List<GabMessage> messages = user.getMessages();
        Sorter sorter = new  Sorter(GabMessage.DESCENDING_COMPARATOR);
        messages = sorter.sort(messages);
        for (GabMessage message : messages) {
            @Inv("+<self>=+c85") Map<String, String> messageMap = message.getTemplateMap();
            // fix up the contents
            String content = messageMap.get("messageContents");
            c85: messageMap.put("messageContents", PageUtils.formatLongString(content, webSession));
            if (!suppressTimestamp) {
                c87: getContentsHelper(builder, messageMap);
            } else {
                c89: messageListTemplateWithoutTime.getEngine().replaceTagsBuilder(messageMap, builder);
            }
        }
        String messageContents = builder.toString();
        @Inv("+<self>=+c94+c95") Map<String, String> userMap = user.getTemplateMap();
        c94: userMap.put("chats", getChatContent(user, webSession));
        c95: userMap.put("messages", messageContents);
        return userTemplate.getEngine().replaceTags(userMap);
    }

    private String getChatContent(GabUser user, WebSession webSession) {
        List<Link> links = new  ArrayList();
        // Get the collection of chats involving the active user
        // and this displayed user
        Collection<GabChat> gabChats = getDb().getChats(webSession.getUserId(), user.getId());
        // Either this is my page or I have an existing chat with this user
        if (webSession.getUserId().equals(user.getId()) || !gabChats.isEmpty()) {
            getChatContentHelper(webSession, gabChats, links);
        } else {
            getChatContentHelper1(links, user);
        }
        @Inv("+<self>=+c112") StringBuilder sb = new  StringBuilder();
        if (!links.isEmpty()) {
            c112: getChatContentHelper2(sb, links);
        }
        return sb.toString();
    }

    @Summary({"builder", "1"})
    private void getContentsHelper(StringBuilder builder, Map<String, String> messageMap) {
        messageListTemplate.getEngine().replaceTagsBuilder(messageMap, builder);
    }

    @Summary({"links", "1"})
    private void getChatContentHelper(WebSession webSession, Collection<GabChat> gabChats, @Inv("gabChats+<self>=+c125-c124") List<Link> links) {
        c124: for (GabChat gabChat : gabChats) {
            c125: links.add(new  Link(ChatHandler.getPathToChat(gabChat.getId()), "Chat with " + gabChat.getOthers(webSession.getUserId())));
        }
    }

    private void getChatContentHelper1(List<Link> links, GabUser user) {
        // No chat exists
        links.add(new  Link(ChatHandler.getPathToNewChat(user.getId()), "Start a chat with " + user.getDisplayName()));
    }

    @Summary({"sb", "1"})
    private void getChatContentHelper2(StringBuilder sb, List<Link> links) {
        sb.append("<h2>Chats</h2><ul>");
        sb.append(menuTemplate.getEngine().replaceTags(links));
        sb.append("</ul>");
    }
}
