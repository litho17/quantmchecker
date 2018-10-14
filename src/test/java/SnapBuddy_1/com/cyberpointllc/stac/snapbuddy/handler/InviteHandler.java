package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
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

public class InviteHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/invite";

    private static final String TITLE = "Invite Friends";

    private static final String FIELD_NAME = "invite";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<tr>" + "    <td>" + "        <input type=\"checkbox\" name=\"" + FIELD_NAME + "\" value=\"{{identity}}\"> " + "    </td>" + "    <td><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>");

    public InviteHandler(SnapService snapService) {
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
        if (context == null) {
            throw new  IllegalArgumentException("Context may not be null");
        }
        Person activePerson = context.getActivePerson();
        @Bound("+ 7 (* 4 snapService.getPeople)") int i;
        @Inv("= (- map it it it) (- (+ c60 c61 c62) c56 c56 c56)") Map<String, String> map = new  HashMap();
        @Inv("= (- sb it) (- (+ c49 c50 c51 c52 c63 c66 c67 c68) c56)") StringBuilder sb = new  StringBuilder();
        c49: sb.append("<form action=\"");
        c50: sb.append(PATH);
        c51: sb.append("\" method=\"post\" enctype=\"multipart/form-data\">");
        c52: sb.append("<table>");
        @Iter("<= it snapService.getPeople") Iterator<String> it = snapService.getPeople().iterator();
        while (it.hasNext()) {
            String identity;
            c56: identity = it.next();
            Person somebody = getSnapService().getPerson(identity);
            if (canInvite(activePerson, snapService.getInvitations(activePerson), somebody)) {
                map.clear();
                c60: map.put("identity", somebody.getIdentity());
                c61: map.put("photoURL", getProfilePhotoUrl(somebody));
                c62: map.put("name", somebody.getName());
                c63: sb.append(TEMPLATE.replaceTags(map));
            }
        }
        c66: sb.append("</table>");
        c67: sb.append("<input type=\"submit\" value=\"Invite\" name=\"submit\" >");
        c68: sb.append("</form>");
        return sb.toString();
    }

    /**
     * Determines if the active Person can invite the somebody Person.
     * All Persons are permitted to be invited except for following:
     * <ul>
     * <li>A Person may not invite themself</li>
     * <li>A Person may not invite an existing friend</li>
     * <li>A Person may not invite someone who is already invited</li>
     * </ul>
     *
     * @param activePerson doing the inviting
     * @param invited      set of Persons who are already involved in an invitation
     * @param somebody     who would like to be invited
     * @return boolean true if somebody can be invited
     */
    private static boolean canInvite(Person activePerson, Set<Person> invited, Person somebody) {
        return ((somebody != null) && !activePerson.getIdentity().equals(somebody.getIdentity()) && !activePerson.getFriends().contains(somebody.getIdentity()) && !invited.contains(somebody));
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person activePerson = getPerson(httpExchange);
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
        @Bound("httpExchange.context.fieldName") int i;
        @Inv("= (- itemStrings it) (- c268 c267)") List<String> itemStrings = new  ArrayList();
        try {
            // get items associated with the field name
            if (fileUpload.parseParameterMap(context).get(FIELD_NAME) != null && !fileUpload.parseParameterMap(context).get(FIELD_NAME).isEmpty()) {
                @Iter("<= it httpExchange.context.fieldName") Iterator<FileItem> it = fileUpload.parseParameterMap(context).get(FIELD_NAME).iterator();
                while (it.hasNext()) {
                    FileItem item;
                    c267: item = it.next();
                    c268: itemStrings.add(item.getString());
                }
            }
        } catch (Exception e) {
            throw new  IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }


        for (String identity : itemStrings) {
            Person invitedPerson = getSnapService().getPerson(identity);
            if (invitedPerson != null) {
                getSnapService().sendInvitation(activePerson, invitedPerson);
            }
        }
        return getDefaultRedirectResponse();
    }
}
