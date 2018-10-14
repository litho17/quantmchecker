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

public class PublicHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/public/";

    private static final String TITLE = "Change Photo Visibility Settings";

    private static final String FIELD_NAME = "public";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<form action=\"" + PATH + "{{pid}}\" method=\"post\" enctype=\"multipart/form-data\">" + "    <center>" + "        <div class=\"photos\"> " + "            <img src=\"{{photoPath}}\" alt=\"{{currentCaption}}\" /><br/>" + "            {{currentCaption}}" + "        </div>" + "        <input type=\"checkbox\" name=\"" + FIELD_NAME + "\" {{isPublic}} />Make Photo Publicly Visible<br/>" + "        <input type=\"submit\" value=\"Change Privacy\" name=\"submit\" />" + "    </center>" + "</form>");

    private final String redirectResponsePath;

    public PublicHandler(SnapService snapService, String redirectResponsePath) {
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
        Photo photo = getSnapService().getPhoto(path);
        boolean isPublic = photo.isPublicPhoto();
        String isCurrentlyPublic = "";
        // box is already checked
        if (isPublic) {
            isCurrentlyPublic = "checked";
        }
        Person activePerson = context.getActivePerson();
        @Bound("4") int i;
        @Inv("= map (+ c55 c56 c57 c58)") Map<String, String> map = new  HashMap();
        if (activePerson.getPhotos().contains(path)) {
            c55: map.put("pid", photo.getIdentity());
            c56: map.put("photoPath", getPhotoUrl(photo));
            c57: map.put("currentCaption", photo.getCaption());
            c58: map.put("isPublic", isCurrentlyPublic);
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
        Person person = getPerson(httpExchange);
        String path = httpExchange.getRequestURI().getPath();
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
        }
        Photo photo = getSnapService().getPhoto(path);
        // we do not change the visibility of profile photos
        if (photo.getIdentity().equals(getProfilePhotoIdentity(person))) {
            return getDefaultRedirectResponse();
        }
        String isPublic = MultipartHelper.getMultipartFieldContent(httpExchange, FIELD_NAME);
        getSnapService().setVisibility(photo, (isPublic != null));
        return getRedirectResponse(redirectResponsePath + photo.getIdentity());
    }
}
