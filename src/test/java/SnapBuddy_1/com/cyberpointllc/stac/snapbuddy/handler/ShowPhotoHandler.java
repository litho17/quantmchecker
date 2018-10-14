package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebTemplate;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.Map;

public class ShowPhotoHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/showphoto/";

    private static final String TITLE = "View Photo";

    private static final String SHOW_PHOTO_RESOURCE = "showphoto.snippet";

    private final WebTemplate TEMPLATE = new  WebTemplate(SHOW_PHOTO_RESOURCE, getClass());

    public ShowPhotoHandler(SnapService snapService) {
        super(snapService);
    }

    @Override
    public String getPath() {
        return PATH;
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
        if (photo == null) {
            return "Photo does not exist: " + path;
        }
        // Is the person allowed to see this photo?
        Person person = context.getActivePerson();
        if (getSnapService().isPhotoVisible(person, photo)) {
            // good to go
            @Bound("3") int i;
            @Inv("= map (+ c56 c57 c58)") Map<String, String> map = new  HashMap();
            map.clear();
            c56: map.put("pid", photo.getIdentity());
            c57: map.put("photoURL", getPhotoUrl(photo));
            c58: map.put("caption", StringUtils.isBlank(photo.getCaption()) ? "" : photo.getCaption());
            return TEMPLATE.getEngine().replaceTags(map);
        }
        return "You're not allowed to see this photo: " + path;
    }
}
