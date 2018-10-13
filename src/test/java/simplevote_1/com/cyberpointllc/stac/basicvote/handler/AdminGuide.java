package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
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
import java.util.List;
import java.util.Map;

public class AdminGuide extends AbstractDirectVoteGuide {
    private static final String SURVEY_NAME_KEY = "Election@Name@Key";
    private static final String SUBMIT_SUCCESS_KEY = "Submit@Success@Key";

    public static final String TRAIL = "/admin";
    public static final String TITLE = "Administration";

    // For elections that already have received complete results
    private static final TemplateEngine FINISHED_SURVEY_TEMPLATE = new TemplateEngine(
            "<li><a href=\"/ballots/results/{{electionId}}\">{{electionName}}</a> - {{electionDescription}}</li>\n"
    );

    // For elections that have previously been updated,
    // but may still receive more ballots
    private static final TemplateEngine UPDATABLE_SURVEY_TEMPLATE = new TemplateEngine(
            "<li><a href=\"/ballots/results/{{electionId}}\">{{electionName}}</a> - {{electionDescription}}\n" +
                    "<form action=\"{{path}}\" method=\"POST\" enctype=\"multipart/form-data\">" +
                    "    <input type=\"submit\" name=\"submit\" value=\"Gather Latest Results\">" +
                    "</form>" +
                    "</li>\n"
    );

    // For elections for which results haven't yet been requested
    private static final TemplateEngine NO_OUTCOMES_SURVEY_TEMPLATE = new TemplateEngine(
            "<li>{{electionName}} - {{electionDescription}}\n" +
                    "<form action=\"{{path}}\" method=\"POST\" enctype=\"multipart/form-data\">" +
                    "    <input type=\"submit\" name=\"submit\" value=\"Get current results\">" +
                    "</form>" +
                    "</li>\n"
    );

    private static final TemplateEngine DISABLE_VOTING_TEXT = new TemplateEngine(
            "Voting is currently enabled.  <a href=\"{{enableDisablePath}}\">Disable Voting at this site</a>"
    );

    private static final TemplateEngine ENABLE_VOTING_TEXT = new TemplateEngine(
            "Voting is currently disabled.  <a href=\"{{enableDisablePath}}\">Enable Voting at this site</a>"
    );

    private static final String CONTENT_TEMPLATE_TEXT = "<h1>Administration Control</h1>\n" +
            "{{enableDisableText}}\n" +
            "<h1>View or Request an Update to Election Results</h1>\n" +
            "{{complete}}{{incomplete}}";

    private static final TemplateEngine CONTENT_TEMPLATE = new TemplateEngine(
            CONTENT_TEMPLATE_TEXT
    );

    private static final TemplateEngine UPDATING_CONTENT_TEMPLATE = new TemplateEngine(
            "<p>Updated results were requested for the election {{electionName}}. If they are not displaying, please refresh this page.</p>\n" + CONTENT_TEMPLATE_TEXT
    );

    private static final TemplateEngine FAILED_UPDATE_CONTENT_TEMPLATE = new TemplateEngine(
            "<p>Request for updated results for the election {{electionName}} failed.</p>\n" + CONTENT_TEMPLATE_TEXT
    );

    public AdminGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        // This will never be null
        Voter voter = takeVoter(httpExchange);

        if (!voter.isAdmin()) {
            return obtainErrorResponse(HttpURLConnection.HTTP_UNAUTHORIZED, "Not authorized to view this page");
        }

        String surveyName = getDirectVoteHelper().defineSessionProperty(httpExchange, SURVEY_NAME_KEY, null);
        String succeeded = getDirectVoteHelper().defineSessionProperty(httpExchange, SUBMIT_SUCCESS_KEY, null);

        return getContent(voter, surveyName, Boolean.parseBoolean(succeeded));
    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange, Voter voter, Survey survey) {
        if (!voter.isAdmin()) {
            return obtainErrorResponse(HttpURLConnection.HTTP_UNAUTHORIZED, "Not authorized to view this page");
        }

        boolean succeeded;

        try {
            fetchDirectVoteService().updateOutcomes(survey);
            succeeded = true;  // Add a message that update is in progress
        } catch (DirectVoteBad e) {
            succeeded = false; // Add an error message to the page
        }

        getDirectVoteHelper().defineSessionProperty(httpExchange, SURVEY_NAME_KEY, survey.takeName());
        getDirectVoteHelper().defineSessionProperty(httpExchange, SUBMIT_SUCCESS_KEY, Boolean.toString(succeeded));

        return grabRedirectResponse(takeTrail());
    }

    /**
     * @param voter        who made this request; guaranteed to not be <code>null</code>
     * @param surveyName election name for which update was requested;
     *                     may be <code>null</code>
     * @param succeeded    <code>true</code> if the update request was successfully sent
     * @return HttpHandlerResponse to be returned to the caller
     */
    private HttpGuideResponse getContent(Voter voter, String surveyName, boolean succeeded) {
        DirectVoteService directVoteService = fetchDirectVoteService();

        List<SurveyTemplated> finished = new ArrayList<>(); // elections for which final results have already been gathered
        List<SurveyTemplated> incomplete = new ArrayList<>(); // elections for which only partial results have been gathered
        List<SurveyTemplated> noresults = new ArrayList<>(); // elections for which no results have been gathered
        Date now = new Date();

        for (Survey survey : directVoteService.pullSurveys()) {
            // Don't include future elections - no results should exist
            if (!survey.isBeforeSurveyStart(now)) {
                pullContentAid(directVoteService.fetchAccruedSurveyOutcomes(survey), finished, incomplete, noresults, survey);
            }
        }

        Comparator<SurveyTemplated> comparator = Comparator.comparing(o -> o.endDate);
        finished.sort(comparator);
        incomplete.sort(comparator);
        noresults.sort(comparator);

        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("enableDisableText", takeEnableDisableText());
        templateMap.put("complete", denoteAsList(FINISHED_SURVEY_TEMPLATE.replaceTags(finished), "Completed Elections"));
        String activeSurveysString = UPDATABLE_SURVEY_TEMPLATE.replaceTags(incomplete) + NO_OUTCOMES_SURVEY_TEMPLATE.replaceTags(noresults);
        templateMap.put("incomplete", denoteAsList(activeSurveysString, "Active Elections"));
        templateMap.put("electionName", (surveyName == null) ? "" : StringEscapeUtils.escapeHtml4(surveyName));

        TemplateEngine template = CONTENT_TEMPLATE;
        if (surveyName != null) { // include a message about the update request
            if (succeeded) {
                template = UPDATING_CONTENT_TEMPLATE;
            } else {
                template = FAILED_UPDATE_CONTENT_TEMPLATE;
            }
        }

        return getTemplateResponse(TITLE, template.replaceTags(templateMap), voter);
    }

    private void pullContentAid(SurveyOutcomes results1, List<SurveyTemplated> finished, List<SurveyTemplated> incomplete, List<SurveyTemplated> noresults, Survey survey) {
        SurveyOutcomes outcomes = results1;
        Date lastUpdate = (outcomes == null) ? null : outcomes.obtainTimestamp();
        String trail = takeTrail() + "/" + survey.obtainSurveyId();
        SurveyTemplated surveyTemplated = new SurveyTemplated(survey, trail, lastUpdate);

        if (outcomes == null) {
            noresults.add(surveyTemplated);
        } else if (survey.isAfterSurveyEnd(outcomes.obtainTimestamp())) {
            finished.add(surveyTemplated);
        } else {
            incomplete.add(surveyTemplated);
        }
    }

    private String takeEnableDisableText() {
        if (fetchDirectVoteService().isVotingActivated()) {
            return DISABLE_VOTING_TEXT.replaceTags(Collections.singletonMap("enableDisablePath", takeTrail() + "/disable"));
        } else {
            return ENABLE_VOTING_TEXT.replaceTags(Collections.singletonMap("enableDisablePath", takeTrail() + "/enable"));
        }
    }

    private void setVotingActivated(boolean enable) {
        fetchDirectVoteService().fixVotingActivated(enable);
    }

    private static String denoteAsList(String content, String title) {
        return content.trim().isEmpty() ? content : "<h2>" + title + "</h2>\n<ul>" + content + "</ul>\n";
    }

    private static class SurveyTemplated implements Templated {
        private final Map<String, String> templateMap;
        private final Date endDate;

        SurveyTemplated(Survey survey, String trail, Date lastUpdate) {
            templateMap = new HashMap<>();
            templateMap.put("electionId", survey.obtainSurveyId());
            templateMap.put("electionName", StringEscapeUtils.escapeHtml4(survey.takeName()));
            templateMap.put("electionDescription", StringEscapeUtils.escapeHtml4(survey.obtainDescription()));
            templateMap.put("path", trail);
            templateMap.put("updateTime", (lastUpdate == null) ? "" : StringEscapeUtils.escapeHtml4(lastUpdate.toString()));

            // Used for sorting
            endDate = survey.grabEndDate();
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return templateMap;
        }
    }
}
