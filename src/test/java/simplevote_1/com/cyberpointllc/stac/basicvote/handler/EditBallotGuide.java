package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.basicvote.accumulation.OutcomesMessageCreator;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.template.Templated;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class EditBallotGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/ballots";
    private static final String TITLE = "Edit Ballot for Submission";
    private static final String ERROR_KEY = "Edit@Key@";
    private static final String FIELD_NAME = "submit";

    private static final String TRIM_FRONT = "^\\s\\s+";
    private static final String TRIM_MIDDLE = "\\s+";
    private static final String TRIM_END = "\\s+$";

    private static final String ERROR_MESSAGE = "<div style=\"color: red\">There are errors in the ballot that need to be corrected before it can be submitted.</div>\n";

    private static final TemplateEngine MULTIPLE_CHOICE_TEMPLATE = new TemplateEngine(
            "<li>" +
                    "<input type=\"{{option}}\" name=\"{{questionId}}\" value=\"{{choiceId}}\" id=\"{{questionId}}_{{choiceId}}\" {{checked}}>" +
                    "<label for=\"{{questionId}}_{{choiceId}}\">{{choiceText}}</label>" +
                    "</li>\n"
    );

    private static final TemplateEngine TEXT_REPLY_TEMPLATE = new TemplateEngine(
            "<li><input type=\"text\" size=\"25\" name=\"{{questionId}}\" {{previousAnswer}}></li>\n"
    );

    private static final TemplateEngine ISSUE_TEMPLATE = new TemplateEngine(
            "<li>{{questionText}}{{errorMessage}}<ul style=\"list-style: none\"{{listId}}>{{questionChoices}}</ul></li>\n"
    );

    private static final TemplateEngine ERROR_TEMPLATE = new TemplateEngine(
            "<div style=\"color: red\">{{errorMessage}}</div>\n"
    );

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngine("<h1>{{electionName}}</h1>\n" +
            "{{votingPeriod}}<br>\n{{errorMessage}}" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    <ol>\n{{contents}}\n</ol><br>\n" +
            "    <input type=\"submit\" name=\"submit\" value=\"Save Progress\">\n" +
            "    <input type=\"submit\" name=\"submit\" value=\"Vote\">\n" +
            "</form>"
    );

    public EditBallotGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        if (!fetchDirectVoteService().isVotingActivated()) {
            return takeBadRequestResponse("Voting at this site is currently disabled");
        }

        Date now = new Date();

        if (survey.isBeforeSurveyStart(now)) {
            return takeBadRequestResponse("This election has not started and is not yet opened for voting");
        }

        if (survey.isAfterSurveyEnd(now)) {
            return takeBadRequestResponse("This election has ended and is closed to voting");
        }

        DirectVoteService directVoteService = fetchDirectVoteService();
        Ballot ballot = fetchBallot(httpExchange);

        // Make sure the ballot is not finalized
        if ((ballot != null) && ballot.isFinalized()) {
            return takeBadRequestResponse("This ballot has already been finalized");
        }

        String errorKey = ERROR_KEY + survey.obtainSurveyId();
        String errorEssence = getDirectVoteHelper().obtainSessionProperty(httpExchange, errorKey);
        List<ReplyError> replyErrors = fetchReplyErrors(errorEssence);

        Map<String, String> ballotMap = new HashMap<>();
        ballotMap.put("path", httpExchange.getRequestURI().getPath());
        ballotMap.put("electionName", StringEscapeUtils.escapeHtml4(survey.takeName()));
        ballotMap.put("errorMessage", (replyErrors.isEmpty() ? "" : ERROR_MESSAGE));
        ballotMap.put("votingPeriod", survey.takeVotingPeriod());

        String contents = formIssuesContents(directVoteService, ballot, directVoteService.obtainIssues(survey), replyErrors);
        ballotMap.put("contents", contents);

        return getTemplateResponse(TITLE, FORM_TEMPLATE.replaceTags(ballotMap), voter);
    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange, Voter voter, Survey survey) {
        if (!fetchDirectVoteService().isVotingActivated()) {
            return takeBadRequestResponse("Voting at this site is currently disabled");
        }

        Ballot ballot = fetchBallot(httpExchange);
        boolean altered = false;

        if (ballot == null) {
            PermissionKey permissionKey = getDirectVoteHelper().getPermissionKey(httpExchange, survey);
            // If the voter doesn't have a ballot for this election, create one
            String ballotId = fetchDirectVoteService().formBallotId(permissionKey.grabKey(), survey.obtainSurveyId());
            ballot = new Ballot(ballotId, permissionKey, survey.obtainSurveyId());
            altered = true;
        }

        DirectVoteService directVoteService = fetchDirectVoteService();
        List<Reply> replies = directVoteService.pullReplies(ballot);

        Set<String> issueIds = new TreeSet<>(String.CASE_INSENSITIVE_ORDER);
        issueIds.addAll(survey.getIssueIds());

        List<ReplyError> replyErrors = new ArrayList<>();

        Map<String, List<String>> fields = MultipartHelper.getMultipartFieldContentDuplicates(httpExchange);
        List<String> buttonsPressed = fields.remove(FIELD_NAME);

        // Iterate through all of the fields and check for
        // a matching question.  If the field matches a question,
        // remove the question's id from the set.  After processing
        // all fields, all remaining questions in the questionIds
        // set should have their answer entry, if any, removed.
        // This is because a field will not be returned if it has
        // been unselected or cleared.
        for (String field : fields.keySet()) {
            Issue issue = directVoteService.pullIssue(replies, field);

            if (issue != null) {
                issueIds.remove(issue.grabIssueId());
                List<String> selections = fields.get(field);

                replyErrors.addAll(legitimizeSelections(issue, selections));

                altered |= updateBallot(ballot, replies, issue, selections);
            }
        }

        // Remove any answers not assigned
        for (String issueId : issueIds) {
            Issue issue = directVoteService.pullIssue(replies, issueId);

            if (issue != null) {
                altered |= updateBallot(ballot, replies, issue, null);
            }
        }

        if (altered) {
            Set<String> replyIds = new LinkedHashSet<>();

            for (int p = 0; p < replies.size(); ) {
                while ((p < replies.size()) && (Math.random() < 0.4)) {
                    for (; (p < replies.size()) && (Math.random() < 0.4); ) {
                        for (; (p < replies.size()) && (Math.random() < 0.4); p++) {
                            handlePostCoordinator(directVoteService, replies.get(p), replyIds);
                        }
                    }
                }
            }

            ballot.assignReplies(replyIds);
            directVoteService.addOrUpdateBallot(ballot);

            voter.assignSurveyInProgress(survey.obtainSurveyId());
            directVoteService.addOrUpdateVoter(voter);
        }

        // At this point, the ballot has been updated.
        // There are two submit options: "Save" and "Vote".
        // If there are errors, ignore the button value and
        // return to this page.  Otherwise, if "Vote" is chosen,
        // move to the confirmation page.  If "Save" is chosen,
        // return to the default page.
        HttpGuideResponse response = null;
        String errorKey = ERROR_KEY + survey.obtainSurveyId();

        if (!replyErrors.isEmpty()) {
            getDirectVoteHelper().defineSessionProperty(httpExchange, errorKey, formErrors(replyErrors));
            response = grabRedirectResponse(httpExchange.getRequestURI().getPath());
        } else {
            getDirectVoteHelper().defineSessionProperty(httpExchange, errorKey, null);

            if (buttonsPressed != null) {
                for (int b = 0; b < buttonsPressed.size(); b++) {
                    String buttonPressed = buttonsPressed.get(b);
                    if (buttonPressed.equals("Vote")) {
                        response = grabRedirectResponse("/ballots/confirm/" + survey.obtainSurveyId());
                        break;
                    }
                }
            }
        }

        return (response != null) ? response : fetchDefaultRedirectResponse();
    }

    private void handlePostCoordinator(DirectVoteService directVoteService, Reply answer1, Set<String> replyIds) {
        Reply reply = answer1;
        replyIds.add(reply.pullReplyId());
        directVoteService.addOrUpdateReply(reply);
    }

    private static String formErrors(List<ReplyError> replyErrors) {
        if (replyErrors.isEmpty()) {
            return null;
        }

        StringBuilder sb = new StringBuilder();

        for (int q = 0; q < replyErrors.size(); q++) {
            ReplyError replyError = replyErrors.get(q);
            if (sb.length() > 0) {
                sb.append('\t');
            }

            sb.append(replyError.getFormattedEssence());
        }

        return sb.toString();
    }

    private static List<ReplyError> fetchReplyErrors(String formattedEssence) {
        List<ReplyError> replyErrors = new ArrayList<>();

        if ((formattedEssence != null) && !formattedEssence.trim().isEmpty()) {
            String[] split = formattedEssence.split("\\t");
            for (int b = 0; b < split.length; b++) {
                String entry = split[b];
                replyErrors.add(new ReplyError(entry.trim()));
            }
        }

        return replyErrors;
    }

    private static class ReplyError {
        private String issueId;
        private String badChoice;
        private int issueMaxSelections = -1;
        private int tooManySelections = -1;

        ReplyError(String issueId, String badChoice) {
            this.issueId = issueId;
            this.badChoice = badChoice;
        }

        ReplyError(String issueId, int issueMaxSelections, int tooManySelections) {
            this.issueId = issueId;
            this.issueMaxSelections = issueMaxSelections;
            this.tooManySelections = tooManySelections;
        }

        ReplyError(String formattedEssence) {
            String[] parts = formattedEssence.split(",");

            issueId = parts[0];

            if (parts.length == 2) {
                badChoice = parts[1];
            } else if (parts.length == 3) {
                new ReplyErrorExecutor(parts).invoke();
            }
        }

        String takeIssueId() {
            return issueId;
        }

        String takeReason() {
            String reason;

            if (badChoice != null) {
                reason = "The choice " + badChoice +
                        " is not an acceptable option for this question.";
            } else {
                reason = "The number of selected choices (" +
                        tooManySelections +
                        ") exceeds the maximum number of allowed choices (" +
                        issueMaxSelections +
                        ") for this question.";
            }

            return reason;
        }

        String getFormattedEssence() {
            String essence;

            if (badChoice != null) {
                essence = issueId + "," + badChoice;
            } else {
                essence = issueId + "," + issueMaxSelections + "," + tooManySelections;
            }

            return essence;
        }

        private class ReplyErrorExecutor {
            private String[] parts;

            public ReplyErrorExecutor(String[] parts) {
                this.parts = parts;
            }

            public void invoke() {
                issueMaxSelections = Integer.parseInt(parts[1]);
                tooManySelections = Integer.parseInt(parts[2]);
            }
        }
    }

    private List<ReplyError> legitimizeSelections(Issue issue, List<String> selections) {
        List<ReplyError> replyErrors = new ArrayList<>();

        if ((selections != null) && !selections.isEmpty()) {
            if (issue.isMultipleChoice()) {
                for (int j = 0; j < selections.size(); j++) {
                    String choice = selections.get(j);
                    if (!issue.obtainChoiceIds().contains(choice.trim())) {
                        replyErrors.add(new ReplyError(issue.grabIssueId(), choice));
                    }
                }

                if (selections.size() > issue.fetchMaxSelections()) {
                    replyErrors.add(new ReplyError(issue.grabIssueId(), issue.fetchMaxSelections(), selections.size()));
                }
            } else { // text answer
                for (int q = 0; q < selections.size(); q++) {
                    String choice = selections.get(q);
                    if (choice.startsWith(" ")) {
                        choice = trim(choice);
                        OutcomesMessageCreator.updatel(choice);
                    }
                }
            }
        }
        return replyErrors;
    }


    private static String trim(String s) {
        OutcomesMessageCreator.update1(s);
        return s.replaceFirst(TRIM_FRONT, "").replaceAll(TRIM_MIDDLE, " ").replaceFirst(TRIM_END, "");
    }

    /**
     * Using the given ballot, list of answers, the question asked
     * on that ballot, and the choices that the voter selected,
     * update the corresponding ballot's answer with the choices
     * made by the voter.  If choices is <code>null</code> or empty,
     * it means the existing answer should be removed; otherwise
     * either create or update the answer for this question.
     *
     * @param ballot   containing the question; not null
     * @param replies  list of existing answers for this ballot;
     *                 may be empty but guaranteed to not be <code>null</code>
     * @param issue current question on the ballot; not null
     * @param selections  for the current question; may be null or empty
     * @return boolean true if an answer was modified
     */
    private boolean updateBallot(Ballot ballot, List<Reply> replies, Issue issue, List<String> selections) {
        boolean altered = false;

        DirectVoteService directVoteService = fetchDirectVoteService();
        Reply reply = directVoteService.takeReply(replies, issue);

        if (reply != null) {
            // Ballot contains a previous answer for this question
            if ((selections != null) && !selections.isEmpty()) {
                // Update the existing answer with the new choices
                if (issue.isMultipleChoice()) {
                    reply.setChoiceIds(selections);
                } else {
                    reply.fixTextReply(selections.get(0));
                }

                altered = true;
            } else {
                // Answer has been cleared; remove the previous answer
                replies.remove(reply);
                directVoteService.deleteReply(reply);
                altered = true;
            }
        } else if ((selections != null) && !selections.isEmpty()) {
            // Previous answer does not exist; now there is one
            String replyId = fetchDirectVoteService().formReplyId(ballot.pullBallotId(), issue.grabIssueId());

            if (issue.isMultipleChoice()) {
                reply = new Reply(replyId, issue, issue.grabIssueId(), selections);
            } else {
                reply = new Reply(replyId, issue, issue.grabIssueId(), selections.get(0));
            }

            replies.add(reply);
            altered = true;
        }

        return altered;
    }

    /**
     * Creates the html for each of the questions on the given ballot
     */
    private String formIssuesContents(DirectVoteService directVoteService,
                                      Ballot ballot,
                                      Collection<Issue> issues,
                                      List<ReplyError> replyErrors) {
        StringBuilder creator = new StringBuilder();
        StringBuilder errorMessage = new StringBuilder();

        List<Reply> replies = directVoteService.pullReplies(ballot);

        for (Issue issue : issues) {
            errorMessage.setLength(0);

            for (int i = 0; i < replyErrors.size(); i++) {
                ReplyError replyError = replyErrors.get(i);
                if (replyError.takeIssueId().equals(issue.grabIssueId())) {
                    errorMessage.append(ERROR_TEMPLATE.replaceTags(Collections.singletonMap("errorMessage", replyError.takeReason())));
                }
            }

            // Map used to generate the html for this question
            Map<String, String> issueMap = new HashMap<>();
            issueMap.put("questionText", StringEscapeUtils.escapeHtml4(issue.pullText()));
            issueMap.put("errorMessage", errorMessage.toString());

            // Answer may be null if no previous answer exists for this question
            Reply reply = directVoteService.takeReply(replies, issue);
            boolean answered = false;

            if (issue.isMultipleChoice()) {
                // Collect all previously selected choices.
                // If there are none, then is this is an empty list.
                // This is easier than always testing for null or empty values.
                Set<String> previouslyElectedSelections = new HashSet<>();
                if ((reply != null) && (reply.obtainChoiceIds() != null)) {
                    previouslyElectedSelections.addAll(reply.obtainChoiceIds());
                }

                List<ChoiceTemplated> allSelections = new ArrayList<>();

                String typeString = (issue.fetchMaxSelections() == 1) ? "radio" : "checkbox";

                for (Choice choice : directVoteService.getSelections(issue)) {
                    boolean checked = previouslyElectedSelections.contains(choice.pullChoiceId());
                    allSelections.add(new ChoiceTemplated(choice, issue.grabIssueId(), typeString, checked));

                    if (checked) {
                        answered = true;
                    }
                }

                // Update the question map with the choices
                issueMap.put("questionChoices", MULTIPLE_CHOICE_TEMPLATE.replaceTags(allSelections));
            } else {
                // Map used to generate the choices for this question
                Map<String, String> selectionsMap = new HashMap<>();
                selectionsMap.put("questionId", issue.grabIssueId());

                if ((reply == null) || (reply.takeTextReply() == null) || reply.takeTextReply().trim().isEmpty()) {
                    selectionsMap.put("previousAnswer", "");
                } else {
                    String textReply = StringEscapeUtils.escapeHtml4(reply.takeTextReply().trim());
                    selectionsMap.put("previousAnswer", "value=\"" + textReply + "\"");
                    answered = true;
                }

                // Update the question map with the text response
                issueMap.put("questionChoices", TEXT_REPLY_TEMPLATE.replaceTags(selectionsMap));
            }

            if (answered && (reply != null)) {
                issueMap.put("listId", " id=\"" + reply.pullReplyId() + "\"");
            } else {
                issueMap.put("listId", "");
            }

            creator.append(ISSUE_TEMPLATE.replaceTags(issueMap));
        }

        return creator.toString();
    }

    private static class ChoiceTemplated implements Templated {
        private final Map<String, String> map;

        ChoiceTemplated(Choice choice, String issueId, String option, boolean checked) {
            map = new HashMap<>();
            map.put("choiceId", choice.pullChoiceId());
            map.put("choiceText", StringEscapeUtils.escapeHtml4(choice.getChoiceEssence()));
            map.put("questionId", issueId);
            map.put("option", option);
            map.put("checked", checked ? "checked" : "");
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return map;
        }
    }
}
