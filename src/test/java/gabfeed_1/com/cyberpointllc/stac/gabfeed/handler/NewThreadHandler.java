package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabMessage;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabRoom;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabThread;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabUser;
import gabfeed_1.com.cyberpointllc.stac.gabfeed.persist.GabDatabase;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSessionService;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebTemplate;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import gabfeed_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.net.HttpURLConnection;
import java.util.Map;

public class NewThreadHandler extends GabHandler {

    private static final String PATH = "/newthread/";

    private final WebTemplate newThreadTemplate;

    public NewThreadHandler(GabDatabase db, WebSessionService webSessionService) {
        super(db, webSessionService);
        this.newThreadTemplate = new  WebTemplate("NewThreadTemplate.html", getClass());
    }

    @Override
    public String getPath() {
        return PATH;
    }

    public static String getPathToPostToRoom(String roomId) {
        return PATH + roomId;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange, String roomId, GabUser user) {
        GabRoom room = getDb().getRoom(roomId);
        if (room == null) {
            return getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid Room: " + roomId);
        }
        return getTemplateResponse(room.getName(), getContents(room), user);
    }

    private String getContents(GabRoom room) {
        @Inv("+<self>=+c49") Map<String, String> threadMap = room.getTemplateMap();
        c49: threadMap.put("path", getPath());
        return newThreadTemplate.getEngine().replaceTags(threadMap);
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange, String roomId, GabUser user) {
        GabRoom room = getDb().getRoom(roomId);
        if (room == null) {
            return getErrorResponse(HttpURLConnection.HTTP_NOT_FOUND, "Invalid Room: " + roomId);
        }
        Map<String, String> fields = MultipartHelper.getMultipartFieldContent(httpExchange);
        GabThread newThread;
        newthreadhandler61: newThread = room.addThread(fields.get("threadName"), user.getId());
        GabMessage message = newThread.addMessage(fields.get("messageContents"), user.getId());
        user.addMessage(message.getId());
        return getRedirectResponse(ThreadHandler.getPathToThread(newThread.getId()));
    }
}
