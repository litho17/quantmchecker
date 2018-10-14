package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.fileupload.FileItem;
import org.apache.commons.fileupload.FileItemFactory;
import org.apache.commons.fileupload.FileUpload;
import org.apache.commons.fileupload.disk.DiskFileItemFactory;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class UnfriendHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/unfriend";

    private static final String TITLE = "Remove Friends";

    private static final String FIELD_NAME = "unfriend";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<tr>" + "    <td rowspan=\"2\">" + "        <input type=\"checkbox\" name=\"unfriend\" value=\"{{identity}}\"> " + "    </td>" + "    <td rowspan=\"2\"><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>" + "<tr><td>{{location}}</td></tr>");

    public UnfriendHandler(SnapService snapService) {
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
        @Bound("+ 7 (* 5 context.activePerson.friends)") int i;
        @Inv("= (- map it it it it) (- (+ c64 c65 c66 c67) c61 c61 c61 c61)") Map<String, String> map = new  HashMap();
        @Inv("= (- sb it) (- (+ c54 c55 c56 c57 c68 c71 c73 c75) c61)") StringBuilder sb = new  StringBuilder();
        // add form
        c54: sb.append("<form action=\"");
        c55: sb.append(PATH);
        c56: sb.append("\" method=\"post\" enctype=\"multipart/form-data\">");
        c57: sb.append("<table>");
        @Iter("<= it context.activePerson.friends") Iterator<String> it = context.activePerson.friends.iterator();
        while (it.hasNext()) {
            String identity;
            c61: identity = it.next();
            Person friend = getSnapService().getPerson(identity);
            if (friend != null) {
                Location location = friend.getLocation();
                String city = Location.UNKNOWN.equals(location) ? "" : location.getCity();
                map.clear();
                c64: map.put("photoURL", getProfilePhotoUrl(friend));
                c65: map.put("name", friend.getName());
                c66: map.put("identity", friend.getIdentity());
                c67: map.put("location", city);
                c68: sb.append(TEMPLATE.replaceTags(map));
            }
        }
        c71: sb.append("</table>");
        // add Unfriend Button
        c73: sb.append("<input type=\"submit\" value=\"Unfriend\" name=\"submit\" >");
        // close form
        c75: sb.append("</form>");
        return sb.toString();
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person person = getPerson(httpExchange);
        @Inv("= (- friends it2) (- c118 c115)") Set<Person> friends = new  HashSet();
        // List<String> identities = MultipartHelper.getMultipartFieldItems(httpExchange, FIELD_NAME);


        if (httpExchange == null) {
            throw new  IllegalArgumentException("HttpExchange may not be null");
        }
        if (StringUtils.isBlank(FIELD_NAME)) {
            throw new  IllegalArgumentException("Field name may not be blank or null");
        }
        MultipartHelper.HttpExchangeRequestContext context = new MultipartHelper.HttpExchangeRequestContext(httpExchange);
        FileUpload fileUpload = new  FileUpload();
        FileItemFactory fileItemFactory = new DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);
        @Bound("* 2 FIELD_NAME") int i;
        @Inv("= (- itemStrings it) (- c268 c267)") List<String> itemStrings = new ArrayList();
        try {
            // get items associated with the field name
            if (fileUpload.parseParameterMap(context).get(FIELD_NAME) != null && !fileUpload.parseParameterMap(context).get(FIELD_NAME).isEmpty()) {
                @Iter("<= it FIELD_NAME") Iterator<FileItem> it = fileUpload.parseParameterMap(context).get(FIELD_NAME).iterator();
                while (it.hasNext()) {
                    FileItem item;
                    c267: item = it.next();
                    c268: itemStrings.add(item.getString());
                }
            }
        } catch (Exception e) {
            throw new  IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        @Iter("<= it2 itemStrings") Iterator<String> it2 = itemStrings.iterator();
        while (it2.hasNext()) {
            String identity;
            c115: identity = it2.next();
            Person friend = getSnapService().getPerson(identity);
            if (friend != null) {
                c118: friends.add(friend);
            }
        }
        getSnapService().removeFriends(person, friends);
        return getDefaultRedirectResponse();
    }
}
