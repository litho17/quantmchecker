package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabMessage;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabThread;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabUser;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSession;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSessionService;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebTemplate;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.net.HttpURLConnection;
import java.util.Map;

public class NewMessageHandler extends GabHandler {

    private static final String PATH = "/newmessage/";

    private final WebTemplate newMessageTemplate;

    public NewMessageHandler(GabDatabase db, WebSessionService webSessionService) {
        super(db, webSessionService);
        this.newMessageTemplate = new  WebTemplate("NewMessageTemplate.html", getClass());
    }

    @Override
    public String getPath() {
        return PATH;
    }

    public static String getPathToPostToThread(String threadId) {
        return PATH + threadId;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange, String threadId, GabUser user) {
        GabThread thread = getDb().getThread(threadId);
        if (thread == null) {
            return getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid Thread: " + threadId);
        }
        return getTemplateResponse(thread.getName(), getContents(thread), user);
    }

    private String getContents(GabThread thread) {
        Map<String, String> threadMap = thread.getTemplateMap();
        threadMap.put("path", getPath());
        return newMessageTemplate.getEngine().replaceTags(threadMap);
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange, String threadId, @Inv("+<self>.messageIds=+67") GabUser user) {
        String query = httpExchange.getRequestURI().getQuery();
        if (!StringUtils.isBlank(query) && query.equals("suppressTimestamp=true")) {
            WebSession webSession = getWebSessionService().getSession(httpExchange);
            webSession.setProperty("suppressTimestamp", "true");
        }
        @Inv("+<self>.messageIds=+66") GabThread thread = getDb().getThread(threadId);
        if (thread == null) {
            return getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid Thread: " + threadId);
        }
        String messageContent = MultipartHelper.getMultipartFieldContent(httpExchange, "messageContents");
        GabMessage message;
        c66: message = thread.addMessage(messageContent, user.getId());
        c67: user.addMessage(message.getId());
        return getRedirectResponse(ThreadHandler.getPathToThread(threadId));
    }
}
