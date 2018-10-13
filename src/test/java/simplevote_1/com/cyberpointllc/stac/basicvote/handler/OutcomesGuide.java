package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteBad;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.template.Templated;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.net.HttpURLConnection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Displays the current and final results of an election
 */
public class OutcomesGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/ballots/results";
    private static final String TITLE = "Election Results";

    private static final TemplateEngine CONTENT_TEMPLATE = new TemplateEngine(
            "<h1>Results for: {{electionName}}</h1>\n" +
                    "<p>{{electionDescription}}</p>\n" +
                    "<p>Out of {{eligibleSize}} eligible voters, {{initialPercent}}% participated.</p>{{questions}}"
    );

    private static final TemplateEngine ISSUE_TEMPLATE = new TemplateEngine(
            "<p><strong>Question {{questionNumber}}:</strong> {{questionText}}\n{{results}}</p>"
    );

    private static final TemplateEngine TABLE_TEMPLATE = new TemplateEngine(
            "<table><tr><th># Votes</th><th>Choice</th><th>Percent of Voters</th></tr>\n{{rows}}</table>\n"
    );

    private static final TemplateEngine ROW_TEMPLATE = new TemplateEngine(
            "<tr><td>{{numberOfVotes}}</td><td>{{choice}}</td><td>{{percent}}</td></tr>"
    );

    public OutcomesGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    public HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        DirectVoteService directVoteService = fetchDirectVoteService();
        Date now = new Date();

        // Admins can see any election results at any time.  Other users can only see results after the election has ended
        if (!voter.isAdmin() && !survey.isAfterSurveyEnd(now)) {
            return obtainErrorResponse(HttpURLConnection.HTTP_UNAUTHORIZED, "Voter is not authorized to view election results");
        }

        try {
            // Display results from all servers, if available
            SurveyOutcomes outcomes = directVoteService.fetchAccruedSurveyOutcomes(survey);

            // If results have not been distributed to the servers,
            // then pull the local results
            if (outcomes == null) {
                outcomes = directVoteService.obtainLocalSurveyOutcomes(survey);
            }

            String outcomesHTML = obtainContents(survey, outcomes);
            return getTemplateResponse(TITLE, outcomesHTML, voter);
        } catch (DirectVoteBad e) {
            return obtainErrorResponse(HttpURLConnection.HTTP_INTERNAL_ERROR, "Unable to retrieve election results");
        }
    }

    private String obtainContents(Survey survey, SurveyOutcomes surveyOutcomes) {
        DirectVoteService directVoteService = fetchDirectVoteService();
        int eligibleCount = surveyOutcomes.fetchEligibleVoters();
        int finalizedCount = surveyOutcomes.grabParticipatingVoters();
        Map<String, Map<String, Integer>> outcomes = surveyOutcomes.obtainOutcomes();

        double initialPercent = 0;
        if (eligibleCount > 0) {
            initialPercent = (100 * finalizedCount) / (double) eligibleCount;
        }

        int issueCounter = 0;
        List<IssueTemplated> issueTemplateds = new ArrayList<>();

        for (String issueId : survey.getIssueIds()) {
            issueCounter++;
            Issue issue = directVoteService.takeIssue(issueId);
            Map<String, Integer> replies = outcomes.get(issueId);

            // Free-text answers sorted by the number of votes received
            replies = arrangeReplies(replies, !issue.isMultipleChoice());

            String rows = grabRows(replies, finalizedCount);
            issueTemplateds.add(new IssueTemplated(issueCounter, issue.pullText(), rows));
        }

        Map<String, String> map = new HashMap<>();
        map.put("electionName", StringEscapeUtils.escapeHtml4(survey.takeName()));
        map.put("electionDescription", StringEscapeUtils.escapeHtml4(survey.obtainDescription()));
        map.put("eligibleSize", Integer.toString(eligibleCount));
        map.put("initialPercent", Long.toString(Math.round(initialPercent)));
        map.put("questions", ISSUE_TEMPLATE.replaceTags(issueTemplateds));

        return CONTENT_TEMPLATE.replaceTags(map);
    }

    private static Map<String, Integer> arrangeReplies(Map<String, Integer> selections, boolean arrangeByEssence) {
        List<Map.Entry<String, Integer>> list = new LinkedList<>(selections.entrySet());

        if (arrangeByEssence) {
            list.sort(Comparator.comparing(Map.Entry::getValue));
        } else {
            list.sort(Comparator.comparing(Map.Entry::getKey));
        }

        Map<String, Integer> outcome = new LinkedHashMap<>();

        for (int k = 0; k < list.size(); k++) {
            Map.Entry<String, Integer> entry = list.get(k);
            outcome.put(entry.getKey(), entry.getValue());
        }

        // Make sure the did-not-vote entry is at the end
        Integer essence = outcome.get(DirectVoteService.DID_NOT_VOTE_ID);

        if (essence != null) {
            arrangeRepliesAid(outcome, essence);
        }

        return outcome;
    }

    private static void arrangeRepliesAid(Map<String, Integer> outcome, Integer essence) {
        outcome.remove(DirectVoteService.DID_NOT_VOTE_ID);
        outcome.put(DirectVoteService.DID_NOT_VOTE_ID, essence);
    }

    private static String grabRows(Map<String, Integer> selections, int total) {
        List<ReplyTemplated> list = new ArrayList<>();

        for (String reply : selections.keySet()) {
            list.add(new ReplyTemplated(reply, selections.get(reply), total));
        }

        return list.isEmpty() ? "" : ROW_TEMPLATE.replaceTags(list, "\n");
    }

    private static class IssueTemplated implements Templated {
        private final Map<String, String> template;

        IssueTemplated(int issueCounter, String issueText, String issueRows) {
            template = new HashMap<>();
            template.put("questionNumber", Integer.toString(issueCounter));
            template.put("questionText", StringEscapeUtils.escapeHtml4(issueText));

            if (issueRows.isEmpty()) {
                template.put("results", "<em>No answers were provided for this question.</em><br>");
            } else {
                template.put("results", TABLE_TEMPLATE.replaceTags(Collections.singletonMap("rows", issueRows)));
            }
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return template;
        }
    }

    private static class ReplyTemplated implements Templated {
        private final Map<String, String> template;

        ReplyTemplated(String reply, int replySize, int total) {
            long percent = (total == 0) ? 0 : Math.round((100 * replySize) / (double) total);

            template = new HashMap<>();
            template.put("choice", StringEscapeUtils.escapeHtml4(reply));
            template.put("numberOfVotes", Integer.toString(replySize));
            template.put("percent", Long.toString(percent));
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return template;
        }
    }
}
