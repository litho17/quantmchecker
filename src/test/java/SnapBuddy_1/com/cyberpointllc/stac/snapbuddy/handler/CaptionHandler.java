package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.Map;
import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

public class CaptionHandler extends AbstractTemplateSnapBuddyHandler {

    private final String redirectResponsePath;

    private static final String PATH = "/editcaption/";

    private static final String TITLE = "Edit Caption";

    private static final String FIELD_NAME = "caption";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<form action=\"" + PATH + "{{pid}}\" method=\"post\" enctype=\"multipart/form-data\">" + "    <center>" + "        <div class=\"photos\"> " + "            <img src=\"{{photoPath}}\" alt=\"{{currentCaption}}\" /><br/>" + "            {{currentCaption}}" + "        </div>" + "        Caption: <input type=\"text\" name=\"" + FIELD_NAME + "\" placeholder=\"{{currentCaption}}\"/> <br/>" + "        <input type=\"submit\" value=\"Update Caption\" name=\"submit\" />" + "    </center> " + "</form>");

    public CaptionHandler(SnapService snapService, String redirectResponsePath) {
        super(snapService);
        this.redirectResponsePath = redirectResponsePath;
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE;
    }

    @Override
    protected String getContents(SnapContext context) {
        String path = context.getPath();
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
        }
        Person activePerson = context.getActivePerson();
        Photo photo = getSnapService().getPhoto(path);
        @Bound("3") int i;
        @Inv("= map (+ c49 c50 c51)") Map<String, String> map = new  HashMap();
        if (activePerson.getPhotos().contains(path)) {
            c49: map.put("pid", photo.getIdentity());
            c50: map.put("photoPath", getPhotoUrl(photo));
            c51: map.put("currentCaption", photo.getCaption());
        } else {
            throw new  IllegalArgumentException("This is not your photo.");
        }
        return TEMPLATE.replaceTags(map);
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        String path = httpExchange.getRequestURI().getPath();
        Person person = getPerson(httpExchange);
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
        }
        Photo photo = getSnapService().getPhoto(path);
        // we do not want to add a caption to the profile photo
        if (photo.getIdentity().equals(getProfilePhotoIdentity(person))) {
            return getDefaultRedirectResponse();
        }
        String newCaption = MultipartHelper.getMultipartFieldContent(httpExchange, FIELD_NAME);
        getSnapService().setCaption(photo, newCaption);
        return getRedirectResponse(redirectResponsePath + photo.getIdentity());
    }
}
