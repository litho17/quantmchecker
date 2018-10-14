package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.sort.Sorter;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class NeighborsHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/neighbors";

    private static final String TITLE = "Neighbors in ";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<tr>" + "    <td><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>");

    public NeighborsHandler(SnapService snapService) {
        super(snapService);
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE + context.getActivePerson().getLocation().getCity();
    }

    @Override
    public String getContents(SnapContext context) {
        assert (context != null) : "Context may not be null";
        Person person = context.getActivePerson();
        @Bound("+ 2 (* 3 snapService.getNeighbors)") int j;
        @Inv("= (- map i i) (- (+ c53 c54) c56 c56)") Map<String, String> map = new  HashMap();
        @Inv("= (- sb i) (- (+ c46 c59 c55) c56)") StringBuilder sb = new  StringBuilder();
        c46: sb.append("<table>");
        Sorter sorter = new  Sorter(Person.ASCENDING_COMPARATOR);
        @InvUnk("Unknown API") List<Person> neighbors = new  ArrayList(snapService.getNeighbors(person));
        neighbors = sorter.sort(neighbors);
        for (@Iter("<= i snapService.getNeighbors") int i = 0; i < neighbors.size(); ) {
            Person neighbor = neighbors.get(i);
            map.clear();
            c53: map.put("photoURL", getProfilePhotoUrl(neighbor));
            c54: map.put("name", neighbor.getName());
            c55:  sb.append(TEMPLATE.replaceTags(map));
            c56: i = i + 1;
        }
        c59: sb.append("</table>");
        return sb.toString();
    }
}
