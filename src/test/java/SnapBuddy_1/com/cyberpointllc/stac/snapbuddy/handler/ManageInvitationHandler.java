package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.net.HttpURLConnection;

public class ManageInvitationHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/invitations";

    private static final String TITLE = "Manage Invitations";

    private static final String FIELD_NAME = "invite";

    private static final String SUBMIT_NAME = "submit";

    private static final Set<String> FIELD_NAMES = new  HashSet(Arrays.asList(FIELD_NAME, SUBMIT_NAME));

    private static final String ACCEPT = "Accept";

    private static final String REJECT = "Reject";

    private static final String INVITATIONS_SENT_TITLE = "<h3>Invitations Sent by You</h3>";

    private static final String INVITATIONS_RECEIVED_TITLE = "<h3>Pending Invitation Requests</h3>";

    private static final String NO_INVITATIONS_SENT = "You have not sent any invitations.";

    private static final String NO_INVITATIONS_RECEIVED = "You have no pending invitations to manage.";

    private static final TemplateEngine INVITATION_SENT_TEMPLATE = new  TemplateEngine("<tr>" + "    <td><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>");

    private static final TemplateEngine INVITATION_RECEIVED_TEMPLATE = new  TemplateEngine("<tr>" + "    <td>" + "        <input type=\"checkbox\" name=\"" + FIELD_NAME + "\" value=\"{{identity}}\"> " + "    </td>" + "    <td><img src=\"{{photoURL}}\" alt=\"{{name}} Profile Photo\" class=\"snapshot\"/></td>" + "    <td>{{name}}</td>" + "</tr>");

    public ManageInvitationHandler(SnapService snapService) {
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
        // Set<Person> invitationsFromThisPerson = getInvitationsSent(activePerson, snapService.getInvitations(activePerson), snapService.getInvitationsTo(activePerson));

        if (snapService.getInvitations(context.activePerson) == null) {
            throw new  IllegalArgumentException("Set of all invited Persons may not be null");
        }
        if (snapService.getInvitationsTo(context.activePerson) == null) {
            throw new  IllegalArgumentException("Set of invitation senders may not be null");
        }
        @Bound("+ (* 3 context.activePerson) (* 4 context.activePerson) context.activePerson 21") int i;
        @Inv("= (- invitationsFromThisPerson it1) (- c81 c80 c84)") Set<Person> invitationsFromThisPerson = new  HashSet();
        @Iter("<= it1 context.activePerson") Iterator<Person> it1 = snapService.getInvitations(context.activePerson).iterator();
        while (it1.hasNext()) {
            Person p1;
            c80: p1 = it1.next();
            c81: invitationsFromThisPerson.add(p1);
        }

        invitationsFromThisPerson.removeAll(snapService.getInvitationsTo(context.activePerson));
        c84: invitationsFromThisPerson.remove(context.activePerson);

        @Inv("= (- sb it2 it3) (- (+ c88 c90 c92 c101 c102 c104 c105 c107 c109 c110 c111 c112 c121 c123 c124 c125 c126 c127 c128 c129 c130 c131 c132 c133 c134) c96 c116)") StringBuilder sb = new  StringBuilder();
        @Inv("= (- map it2 it2 it3 it3 it3) (- (+ c98 c99 c118 c119 c120) c96 c96 c116 c116 c116)") Map<String, String> map = new  HashMap();
        c88: sb.append(INVITATIONS_SENT_TITLE);
        if (invitationsFromThisPerson.isEmpty()) {
            c90: sb.append(NO_INVITATIONS_SENT);
        } else {
            c92: sb.append("<table>");
            @Iter("<= it2 invitationsFromThisPerson") Iterator<Person> it2 = invitationsFromThisPerson.iterator();
            while (it2.hasNext()) {
                Person invited;
                c96: invited = it2.next();
                map.clear();
                c98: map.put("photoURL", getProfilePhotoUrl(invited));
                c99: map.put("name", invited.getName());
                c101: sb.append(INVITATION_SENT_TEMPLATE.replaceTags(map));
            }
            c102: sb.append("</table>");
        }
        c104: sb.append("<hr>");
        c105: sb.append(INVITATIONS_RECEIVED_TITLE);
        if (snapService.getInvitationsTo(context.activePerson).isEmpty()) {
            c107: sb.append(NO_INVITATIONS_RECEIVED);
        } else {
            c109: sb.append("<form action=\"");
            c110: sb.append(PATH);
            c111: sb.append("\" method=\"post\" enctype=\"multipart/form-data\">");
            c112: sb.append("<table>");
            @Iter("<= it3 context.activePerson") Iterator<Person> it3 = snapService.getInvitationsTo(context.activePerson).iterator();
            while (it3.hasNext()) {
                Person sender;
                c116: sender = it3.next();
                map.clear();
                c118: map.put("identity", sender.getIdentity());
                c119: map.put("photoURL", getProfilePhotoUrl(sender));
                c120: map.put("name", sender.getName());
                c121: sb.append(INVITATION_RECEIVED_TEMPLATE.replaceTags(map));
            }
            c123: sb.append("</table>");
            c124: sb.append("<input type=\"submit\" value=\"");
            c125: sb.append(ACCEPT);
            c126: sb.append("\" name=\"");
            c127: sb.append(SUBMIT_NAME);
            c128: sb.append("\" >");
            c129: sb.append("<input type=\"submit\" value=\"");
            c130: sb.append(REJECT);
            c131: sb.append("\" name=\"");
            c132: sb.append(SUBMIT_NAME);
            c133: sb.append("\" >");
            c134: sb.append("</form>");
        }
        return sb.toString();
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person activePerson = getPerson(httpExchange);
        @InvUnk("Nested lists") Map<String, List<String>> multipartValues = MultipartHelper.getMultipartValues(httpExchange, FIELD_NAMES);
        int conditionObj0 = 1;
        if ((multipartValues.get(SUBMIT_NAME) == null) || (multipartValues.get(SUBMIT_NAME).size() != conditionObj0)) {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "Either " + ACCEPT + " or " + REJECT + " must be submitted");
        }
        boolean doAccept;
        if (ACCEPT.equals(multipartValues.get(SUBMIT_NAME).get(0))) {
            doAccept = true;
        } else if (REJECT.equals(multipartValues.get(SUBMIT_NAME).get(0))) {
            doAccept = false;
        } else {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "Either " + ACCEPT + " or " + REJECT + " must be submitted");
        }
        if ((multipartValues.get(FIELD_NAME) != null) && !multipartValues.get(FIELD_NAME).isEmpty()) {
            for (String identity : multipartValues.get(FIELD_NAME)) {
                Person otherPerson = getSnapService().getPerson(identity);
                if (otherPerson != null) {
                    if (doAccept) {
                        getSnapService().acceptInvitation(activePerson, otherPerson);
                    } else {
                        getSnapService().rejectInvitation(activePerson, otherPerson);
                    }
                }
            }
        }
        return getDefaultRedirectResponse();
    }
}
