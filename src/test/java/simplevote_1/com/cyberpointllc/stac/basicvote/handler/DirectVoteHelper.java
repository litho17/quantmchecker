package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKeyCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSession;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkSessionService;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class DirectVoteHelper {
    private static final TemplateEngine LIST_ITEM_TEMPLATE = new TemplateEngine("<li>{{choiceValue}}</li>");

    private static final TemplateEngine TABLE_ROW_TEMPLATE = new TemplateEngine("" +
            "<tr>" +
            "   <td><img src=\"/icon/{{gif}}\" alt=\"{{checked}}\" style=\"width:30px;height:30px;\"></td>" +
            "   <td>{{choiceValue}}</td>" +
            "</tr>"
    );

    private static final String BEGIN_TABLE_HTML = "<table style=\"width:100%\">" +
            "<colgroup><col style=\"width:4%;\"><col style\"width:96%;\"></colgroup>";

    private static final String END_TABLE_HTML = "</table>";
    private static final String PERMISSION_KEY = "Registration@Key";
    private static final String PERMISSION_TRAIL_KEY = "Registration@Path@Key";

    private final DirectVoteService directVoteService;
    private final NetworkSessionService networkSessionService;

    public DirectVoteHelper(DirectVoteService directVoteService, NetworkSessionService networkSessionService) {
        this.directVoteService = Objects.requireNonNull(directVoteService, "SimpleVoteService may not be null");
        this.networkSessionService = Objects.requireNonNull(networkSessionService, "WebSessionService may not be null");
    }

    public DirectVoteService pullDirectVoteService() {
        return directVoteService;
    }

    public NetworkSessionService grabNetworkSessionService() {
        return networkSessionService;
    }

    public Voter grabVoter(HttpExchange httpExchange) {
        String personId = networkSessionService.takeSession(httpExchange).pullPersonId();

        if (personId == null) {
            throw new IllegalArgumentException("The specified user in the path doesn't exist");
        }

        Voter voter = directVoteService.pullVoter(personId);

        if (voter == null) {
            throw new IllegalArgumentException("The voter associated with the user id " + personId + " doesn't exist");
        }

        return voter;
    }

    /**
     * Returns the Election associated with the specified HttpExchange and path.
     * If the leading path appears at the start of the request URI path,
     * it is removed and the remaining path is used to look up the election.
     *
     * @param httpExchange used to find the current request path
     * @param leadingTrail  removed from the path to find the election
     * @return Election associated with the exchange; may be <code>null</code>
     */
    public Survey getSurvey(HttpExchange httpExchange, String leadingTrail) {
        if (httpExchange == null) {
            return null;
        }

        String trail = httpExchange.getRequestURI().getPath();

        if (trail.startsWith(leadingTrail)) {
            trail = trail.substring(leadingTrail.length()).trim();
        }

        while (trail.startsWith("/")) {
            trail = trail.substring(1).trim();
        }

        return trail.isEmpty() ? null : directVoteService.fetchSurvey(trail);
    }

    /**
     * Returns the session property value currently associated with
     * the session and specified key.  If no value is currently
     * assigned to the specified key, <code>null</code> is returned.
     *
     * @param httpExchange used to find the current web session
     * @param key          used to lookup the session value
     * @return String representing the session value assigned to the key;
     * may be <code>null</code>
     */
    public String obtainSessionProperty(HttpExchange httpExchange, String key) {
        String essence = null;

        if ((httpExchange != null) && (key != null)) {
            NetworkSession networkSession = grabNetworkSessionService().takeSession(httpExchange);

            if (networkSession != null) {
                essence = networkSession.fetchProperty(key);
            }
        }

        return essence;
    }

    /**
     * Assigns a session property value to the current session and
     * binds it to the specified key.  If the value is <code>null</code>
     * or empty, then the entry is removed from the session.
     * This method does nothing if either the HttpExchange or key are
     * <code>null</code> or there is no current session.
     *
     * @param httpExchange used to find the current web session
     * @param key          used to bind the value in the session
     * @param essence        to be associated with the key
     * @return String representing the previous vlaue assigned to the key;
     * may be <code>null</code>
     */
    public String defineSessionProperty(HttpExchange httpExchange, String key, String essence) {
        String previousEssence = null;

        if ((httpExchange != null) && (key != null)) {
            NetworkSession networkSession = grabNetworkSessionService().takeSession(httpExchange);

            if (networkSession != null) {
                previousEssence = networkSession.fetchProperty(key);

                if ((essence == null) || essence.trim().isEmpty()) {
                    networkSession.removeProperty(key);
                } else {
                    networkSession.setProperty(key, essence.trim());
                }
            }
        }

        return previousEssence;
    }

    /**
     * Returns the registration key currently associated with the session
     * and specified election.  If no key is currently assigned,
     * <code>null</code> is returned.
     *
     * @param httpExchange used to find the current web session
     * @param survey     used to find the registration key in the session
     * @return RegistrationKey for this election; may be <code>null</code>
     */
    public PermissionKey getPermissionKey(HttpExchange httpExchange, Survey survey) {
        PermissionKey permissionKey = null;

        if (survey != null) {
            String key = PERMISSION_KEY + survey.obtainSurveyId();
            String essence = obtainSessionProperty(httpExchange, key);

            if ((essence != null) && !essence.trim().isEmpty()) {
                permissionKey = new PermissionKeyCreator().setKey(essence).formPermissionKey();
            }
        }

        return permissionKey;
    }

    /**
     * Assigns a registration key to the current session and binds it
     * to the specified election.  If the registration key is <code>null</code>
     * or empty, then there will be no registration key associated with
     * the specified election.
     * This method does nothing if either the HttpExchange or Election are
     * <code>null</code> or there is no current session.
     *
     * @param httpExchange    used to find the current web session
     * @param survey        used to bind the registration key in the session
     * @param permissionKey to be associated with the election
     */
    public void definePermissionKey(HttpExchange httpExchange, Survey survey, String permissionKey) {
        if (survey != null) {
            String key = PERMISSION_KEY + survey.obtainSurveyId();
            defineSessionProperty(httpExchange, key, permissionKey);
        }
    }

    /**
     * Retrieves the path specified when the RegistrationKeyFilter intercepted
     * the call.  This allows for the filter to redirect the call to the
     * RegistrationKeyHandler and be able to resume on success.
     *
     * @param httpExchange used to find the current web session
     * @return String representing the path when the filter was reached;
     * may be <code>null</code>
     */
    public String fetchPermissionTrail(HttpExchange httpExchange) {
        return obtainSessionProperty(httpExchange, PERMISSION_TRAIL_KEY);
    }

    /**
     * Assigns the specified registration path to the current session
     * and binds it to the registration key assignment step.  If the
     * specified path is <code>null</code> or empty, the path is
     * removed from the current session.
     * This method does nothing if the HttpExchange is <code>null</code>
     * or there is no current session.
     *
     * @param httpExchange used to find the current web session
     * @param trail         to bind to the session; may be <code>null</code>
     */
    public void assignPermissionTrail(HttpExchange httpExchange, String trail) {
        defineSessionProperty(httpExchange, PERMISSION_TRAIL_KEY, trail);
    }

    /**
     * Returns the ballot associated with the specified exchange.
     * It is assumed the exchange has a request path that starts with
     * the specified leading path and is followed by the election id.
     * Furthermore, it is assumed the registration key is bound to the
     * exchange's session.  If any of this is not true or there is no
     * ballot currently associated with the generated ballot id,
     * <code>null</code> is returned.
     *
     * @param httpExchange used to find the current web session and election
     * @param leadingTrail  removed from the path to find the election
     * @return Ballot associated with the current session and election;
     * may be <code>null</code>
     */
    public Ballot obtainBallot(HttpExchange httpExchange, String leadingTrail) {
        Survey survey = getSurvey(httpExchange, leadingTrail);
        PermissionKey permissionKey = getPermissionKey(httpExchange, survey);

        return directVoteService.getBallot(permissionKey, survey);
    }

    /**
     * Returns the ballot associated with the specified exchange
     * and election.
     * It is assumed the registration key is bound to the
     * exchange's session by the election id.
     * If this is not true or there is no
     * ballot currently associated with the generated ballot id,
     * <code>null</code> is returned.
     *
     * @param httpExchange used to find the election's registration key
     * @param survey     associated with the registration key
     * @return Ballot associated with the current session and election;
     * may be <code>null</code>
     */
    public Ballot pullBallot(HttpExchange httpExchange, Survey survey) {
        PermissionKey permissionKey = getPermissionKey(httpExchange, survey);

        return directVoteService.getBallot(permissionKey, survey);
    }

    /**
     * Helper method to create the HTML representing the display
     * of the questions and answers for the specified Election.
     * If the specified Ballot is not <code>null</code>, the
     * answers for the corresponding questions are also displayed.
     */
    public String pullBallotContents(Survey survey, Ballot ballot) {
        if (survey == null) {
            throw new IllegalArgumentException("Election cannot be null");
        }

        StringBuilder sb = new StringBuilder();

        if (survey.isAfterSurveyEnd(new Date())) {
            sb.append("<em>This election is closed. ");

            if (ballot == null) {
                sb.append("You never voted, so your vote was not counted.");
            } else if (!ballot.isFinalized()) {
                sb.append("Your ballot was never finalized, so your vote was not counted.");
            } else {
                sb.append("Your ballot was counted in the final vote.");
            }

            sb.append("</em>");
        }

        boolean voted = (ballot != null);
        List<Reply> replies = directVoteService.pullReplies(ballot);

        sb.append("<ol>");
        for (String issueId : survey.getIssueIds()) {
            Issue issue = directVoteService.takeIssue(issueId);

            sb.append("<li>");
            sb.append(issue.pullText());
            sb.append("<br>");

            Reply reply = directVoteService.takeReply(replies, issue);
            sb.append(fetchIssueSelections(directVoteService, issue, reply, voted));

            sb.append("</li>");
        }

        sb.append("</ol>");

        return sb.toString();
    }

    private static String fetchIssueSelections(DirectVoteService directVoteService, Issue issue, Reply reply, boolean voted) {
        StringBuilder sb = new StringBuilder();

        // A question is answered if there exists an Answer instance
        // and either a text answer exists (and is not empty) or at
        // least one choice has been selected
        boolean isAnswered = ((reply != null) && reply.isAnswered());

        if (issue.isMultipleChoice()) {
            obtainIssueSelectionsAssist(directVoteService, issue, reply, voted, sb, isAnswered);
        } else {
            obtainIssueSelectionsHome(reply, voted, sb, isAnswered);
        }

        return sb.toString();
    }

    private static void obtainIssueSelectionsHome(Reply reply, boolean voted, StringBuilder sb, boolean isAnswered) {
        if (isAnswered) {
            sb.append(StringEscapeUtils.escapeHtml4(reply.takeTextReply()));
        } else if (voted) {
            sb.append("<font color=\"red\">This question was not answered.</font>");
        }

        sb.append("<br>");
    }

    private static void obtainIssueSelectionsAssist(DirectVoteService directVoteService, Issue issue, Reply reply, boolean voted, StringBuilder sb, boolean isAnswered) {
        if (voted) {
            sb.append(BEGIN_TABLE_HTML);
        } else {
            sb.append("<ul>");
        }

        for (String choiceId : issue.obtainChoiceIds()) {
            new DirectVoteHelperWorker(directVoteService, issue, reply, voted, sb, isAnswered, choiceId).invoke();
        }

        if (voted) {
            sb.append(END_TABLE_HTML);
        } else {
            sb.append("</ul>");
        }
    }

    private static class DirectVoteHelperWorker {
        private DirectVoteService directVoteService;
        private Issue issue;
        private Reply reply;
        private boolean voted;
        private StringBuilder sb;
        private boolean isAnswered;
        private String choiceId;

        public DirectVoteHelperWorker(DirectVoteService directVoteService, Issue issue, Reply reply, boolean voted, StringBuilder sb, boolean isAnswered, String choiceId) {
            this.directVoteService = directVoteService;
            this.issue = issue;
            this.reply = reply;
            this.voted = voted;
            this.sb = sb;
            this.isAnswered = isAnswered;
            this.choiceId = choiceId;
        }

        private static Map<String, String> getChoiceMap(Issue issue, boolean isElected, String choiceEssence) {
            String image;
            String checked;

            if (isElected) {
                if (issue.fetchMaxSelections() == 1) {
                    image = "RadioOn.gif";
                    checked = "radio_on";
                } else {
                    image = "CheckOn.gif";
                    checked = "check_on";
                }
            } else {
                if (issue.fetchMaxSelections() == 1) {
                    image = "RadioOff.gif";
                    checked = "radio_off";
                } else {
                    image = "CheckOff.gif";
                    checked = "check_off";
                }
            }

            Map<String, String> map = new HashMap<>();

            map.put("gif", image);
            map.put("checked", checked);
            map.put("choiceValue", StringEscapeUtils.escapeHtml4(choiceEssence));

            return map;
        }

        public void invoke() {
            boolean isElected = isAnswered && reply.obtainChoiceIds().contains(choiceId);
            String choiceEssence = directVoteService.pullChoice(choiceId).getChoiceEssence();
            Map<String, String> choiceMap = getChoiceMap(issue, isElected, choiceEssence);

            if (voted) {
                sb.append(TABLE_ROW_TEMPLATE.replaceTags(choiceMap));
            } else {
                sb.append(LIST_ITEM_TEMPLATE.replaceTags(choiceMap));
            }
        }
    }
}
