package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.sort.Sorter;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class FriendsPhotosHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/friendsphotos";

    private static final String TITLE = "My Friends' Photos";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<li><a href=\"showphoto/{{pid}}\"><img src=\"{{photoURL}}\" alt=\"{{caption}}\" class=\"snapshot\"/></a></li>");

    public FriendsPhotosHandler(SnapService snapService) {
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
    public String getContents(SnapContext context) {
        assert (context != null) : "Context may not be null";
        @InvUnk("Nested lists") Map<String, String> map = new  HashMap();
        @InvUnk("Nested lists") StringBuilder sb = new  StringBuilder();
        c44: sb.append("<ul class=\"photos\">");
        @Inv("= (- friends it1) (- c50 c49)") List<Person> friends = new  ArrayList();
        @Iter("<= it context.activePerson") Iterator<String> it1 = context.activePerson.getFriends().iterator();
        while (it1.hasNext()) {
            String identity;
            c49: identity = it1.next();
            c50: friends.add(snapService.getPerson(identity));
        }
        Sorter sorter = new  Sorter(Person.ASCENDING_COMPARATOR);
        friends = sorter.sort(friends);
        for (int i = 0; i < friends.size(); i++) {
            Person friend = friends.get(i);
            if (friend != null) {
                for (String photoId : friend.photos) {
                    Photo photo = getSnapService().getPhoto(photoId);
                    if (photo != null) {
                        map.clear();
                        c61: map.put("pid", photo.getIdentity());
                        c62: map.put("photoURL", getThumbPhotoUrl(photo));
                        c63: map.put("caption", StringUtils.isBlank(photo.getCaption()) ? "" : photo.getCaption());
                        c64: sb.append(TEMPLATE.replaceTags(map));
                    }
                }
            }
        }
        c69: sb.append("</ul>");
        return sb.toString();
    }
}
