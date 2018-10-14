package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.sort.Sorter;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class FriendsHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/friends";

    private static final String TITLE = "Friends";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<tr>" + "    <td rowspan=\"2\"><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>" + "<tr><td>{{location}}</td></tr>");

    public FriendsHandler(SnapService snapService) {
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
        @Bound("+ 2 (* 5 context.activePerson)") int l;
        @Inv("= (- map i i i) (- (+ c60 c61 c62) c65 c65 c65)") Map<String, String> map = new  HashMap();
        @Inv("= (- sb i) (- (+ c63 c67 c43) c65)") StringBuilder sb = new  StringBuilder();
        c43: sb.append("<table>");
        @Inv("= (- friends it) (- c50 c49)") List<Person> friends = new  ArrayList();
        SnapService snapService = getSnapService();
        @Iter("<= it context.activePerson") Iterator<String> it = context.activePerson.getFriends().iterator();
        while (it.hasNext()) {
            String identity;
            c49: identity = it.next();
            c50: friends.add(snapService.getPerson(identity));
        }
        Sorter sorter = new  Sorter(Person.ASCENDING_COMPARATOR);
        friends = sorter.sort(friends);
        for (@Iter("<= i friends") int i = 0; i < friends.size(); ) {
            Person friend = friends.get(i);
            if (friend != null) {
                Location location = friend.getLocation();
                String city = Location.UNKNOWN.equals(location) ? "" : location.getCity();
                map.clear();
                c60: map.put("photoURL", getProfilePhotoUrl(friend));
                c61: map.put("name", friend.getName());
                c62: map.put("location", city);
                c63: sb.append(TEMPLATE.replaceTags(map));
            }
            c65: i = i + 1;
        }
        c67: sb.append("</table>");
        return sb.toString();
    }
}
