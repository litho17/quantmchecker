package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.net.HttpURLConnection;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.ImageService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

public class ProfilePhotoHandler extends AbstractTemplateSnapBuddyHandler {

    private final ImageService imageService;

    private static final String PATH = "/profilephoto";

    private static final String TITLE = "Change Profile Photo";

    private static final String FIELD_NAME = "addprofilephoto";

    private static final String CONTENTS = "<form action=\"" + PATH + "\" method=\"post\" enctype=\"multipart/form-data\">" + "    <label for=\"file\"> Photo: </label>" + "    <input type=\"file\" id=\"file\" name=\"" + FIELD_NAME + "\" autofocus accept=\"image/*\"/>" + "    <br/>" + "    <input type=\"submit\" value=\"Add Photo\" name=\"submit\">" + "</form>";

    public ProfilePhotoHandler(SnapService snapService, ImageService imageService) {
        super(snapService);
        this.imageService = imageService;
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE;
    }

    @Override
    protected String getContents(SnapContext context) {
        return CONTENTS;
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person person = getPerson(httpExchange);
        String id = person.getIdentity();
        SnapService snapService = getSnapService();
        @Bound("1") int i;
        @Inv("= allFieldNames c58") Set<String> allFieldNames = new  HashSet<String>();
        c58: allFieldNames.add(FIELD_NAME);
        Path destDir = Paths.get(imageService.getBasePhotosPath().toString(), id);
        MultipartHelper.getMultipartPhoto(httpExchange, allFieldNames, FIELD_NAME, destDir, getProfilePhotoName());
        // make profile photo
        String photoPath = id + "/" + getProfilePhotoName();
        Photo photo = new  Photo(photoPath, true, null, null, null);
        // check that the image isn't too big
        if (!imageService.isSmallPhoto(photo)) {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "The dimensions of the image are too large");
        }
        snapService.addPhoto(person, photo);
        return getDefaultRedirectResponse();
    }
}
