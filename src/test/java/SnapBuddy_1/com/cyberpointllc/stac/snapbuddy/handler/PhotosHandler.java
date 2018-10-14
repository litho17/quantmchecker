package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.Iterator;
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
        @Bound("+ (* 4 context.activePerson) 2") int i;
        @Inv("= (- map it it it) (- (+ c52 c53 c54) c48 c48 c48)") Map<String, String> map = new  HashMap();
        @Inv("= (- sb it) (- (+ c42 c55 c58) c48)") StringBuilder sb = new  StringBuilder();
        c42: sb.append("<ul class=\"photos\">");
        @Iter("<= it context.activePerson") Iterator<String> it = context.activePerson.photos.iterator();
        while (it.hasNext()) {
            String photoIdentity;
            c48: photoIdentity = it.next();
            Photo photo = getSnapService().getPhoto(photoIdentity);
            if (photo != null) {
                map.clear();
                c52: map.put("pid", photo.getIdentity());
                c53: map.put("photoURL", getThumbPhotoUrl(photo));
                c54: map.put("caption", StringUtils.isBlank(photo.getCaption()) ? "" : photo.getCaption());
                c55: sb.append(TEMPLATE.replaceTags(map));
            }
        }
        c58: sb.append("</ul>");
        return sb.toString();
    }
}
