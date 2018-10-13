package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import org.apache.commons.lang3.StringUtils;
import java.util.Map;

public class PhotosHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/photos";

    private static final String TITLE = "My Photos";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<li><a href=\"editphoto/{{pid}}\"><img src=\"{{photoURL}}\" alt=\"{{caption}}\" class=\"snapshot\"/></a></li>");

    public PhotosHandler(SnapService snapService) {
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
        assert (context != null) : "Context may not be null";
        Person person = context.getActivePerson();
        Map<String, String> map = new  HashMap();
        StringBuilder sb = new  StringBuilder();
        sb.append("<ul class=\"photos\">");
        for (String photoIdentity : person.getPhotos()) {
            Photo photo = getSnapService().getPhoto(photoIdentity);
            if (photo != null) {
                map.clear();
                map.put("pid", photo.getIdentity());
                map.put("photoURL", getThumbPhotoUrl(photo));
                map.put("caption", StringUtils.isBlank(photo.getCaption()) ? "" : photo.getCaption());
                sb.append(TEMPLATE.replaceTags(map));
            }
        }
        sb.append("</ul>");
        return sb.toString();
    }
}
