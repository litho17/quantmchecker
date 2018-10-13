package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.template.Templated;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkTemplate;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ShowSurveysGuide extends AbstractDirectVoteGuide {
    public static final String TRAIL = "/elections";
    public static final String TITLE = "Elections";

    private static final TemplateEngine SURVEY_TEMPLATE = new TemplateEngine(
            "<li id=\"{{electionId}}\">{{electionName}} - {{electionDescription}}<br>" +
                    "{{votingPeriod}}</li>\n"
    );

    private static final TemplateEngine FUTURE_NAME_TEMPLATE = new TemplateEngine(
            "{{electionName}}"
    );

    private static final TemplateEngine ACTIVE_NAME_TEMPLATE = new TemplateEngine(
            "<a href=\"/ballots/{{electionId}}\">{{electionName}}</a> {{icon}}"
    );

    private static final TemplateEngine PAST_NAME_TEMPLATE = new TemplateEngine(
            "<a href=\"/ballots/responses/{{electionId}}\">{{electionName}}</a> <a href=\"/ballots/results/{{electionId}}\">{{icon}}</a>"
    );

    private static final NetworkTemplate SHOW_SURVEYS_TEMPLATE = new NetworkTemplate("ShowElectionsTemplate.html", ShowSurveysGuide.class);

    public ShowSurveysGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        DirectVoteService directVoteService = fetchDirectVoteService();
        Voter voter = takeVoter(httpExchange);

        List<SurveyTemplated> future = new ArrayList<>();
        List<SurveyTemplated> current = new ArrayList<>(); // current but already finalized
        List<SurveyTemplated> past = new ArrayList<>();
        List<SurveyTemplated> active = new ArrayList<>(); // current and not yet finalized
        Date now = new Date();

        for (Survey survey : directVoteService.pullSurveys()) {
            boolean isEligible = voter.isEligible(survey.obtainSurveyId());
            boolean isFuture = survey.isBeforeSurveyStart(now);
            boolean isActive = survey.isSurveyActive(now);

            SurveyTemplated surveyTemplated = new SurveyTemplated(survey, isEligible, isFuture, isActive);

            if (isFuture) {
                // This is an election in the future.
                future.add(surveyTemplated);
            } else if (isActive) {
                // This is a current election
                if (voter.isSurveyFinalized(survey.obtainSurveyId())) {
                    surveyTemplated.fixIcon("<img src=\"/icon/VoteBox.gif\" alt=\"voted\" style=\"height:16px;width:16px;\">");
                    current.add(surveyTemplated);
                } else if (voter.isSurveyInProgress(survey.obtainSurveyId())) {
                    surveyTemplated.fixIcon("<img src=\"/icon/Incomplete.gif\" alt=\"in_progress\" style=\"height:16px;width:16px\">");
                    active.add(surveyTemplated);
                } else {
                    active.add(surveyTemplated);
                }
            } else {
                // This election ended - happened in the past
                if (voter.isSurveyFinalized(survey.obtainSurveyId())) {
                    // Show the results including the (finalized) ballot
                    surveyTemplated.fixIcon("<img src=\"/icon/VoteBox.gif\" alt=\"voted\" style=\"height:16px;width:16px;\">");
                } else {
                    // No ballot was cast or it was invalidated, show the results
                    surveyTemplated.fixIcon("(Results)");
                }

                past.add(surveyTemplated);
            }
        }

        Collections.sort(future);
        Collections.sort(current);
        Collections.sort(past);
        Collections.reverse(past);
        Collections.sort(active);

        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("future", takeListContent(SURVEY_TEMPLATE.replaceTags(future)));
        templateMap.put("current", takeListContent(SURVEY_TEMPLATE.replaceTags(current))); // these are finalized, so can't edit anymore
        templateMap.put("past", takeListContent(SURVEY_TEMPLATE.replaceTags(past)));
        templateMap.put("active", takeListContent(SURVEY_TEMPLATE.replaceTags(active)));

        return getTemplateResponse(TITLE, SHOW_SURVEYS_TEMPLATE.pullEngine().replaceTags(templateMap), voter);
    }

    private static String takeListContent(String content) {
        if (!content.trim().isEmpty()) {
            content = "<ul>\n" + content + "\n</ul>";
        }

        return content;
    }

    private static class SurveyTemplated implements Templated, Comparable<SurveyTemplated> {
        private final Survey survey;
        private final Map<String, String> nameMap;
        private final TemplateEngine engine;

        SurveyTemplated(Survey survey, boolean isEligible, boolean isFuture, boolean isActive) {
            this.survey = survey;

            nameMap = new HashMap<>();
            nameMap.put("electionId", survey.obtainSurveyId());
            nameMap.put("electionName", StringEscapeUtils.escapeHtml4(survey.takeName()));
            nameMap.put("icon", ""); // Value may be changed during processing

            if (isFuture) {
                engine = FUTURE_NAME_TEMPLATE;
            } else if (isActive) {
                engine = isEligible ? ACTIVE_NAME_TEMPLATE : FUTURE_NAME_TEMPLATE;
            } else {
                engine = isEligible ? PAST_NAME_TEMPLATE : FUTURE_NAME_TEMPLATE;
            }
        }

        public void fixIcon(String essence) {
            nameMap.put("icon", essence);
        }

        @Override
        public Map<String, String> getTemplateMap() {
            Map<String, String> templateMap = new HashMap<>();

            templateMap.put("electionId", survey.obtainSurveyId());
            templateMap.put("electionName", engine.replaceTags(nameMap));
            templateMap.put("electionDescription", StringEscapeUtils.escapeHtml4(survey.obtainDescription()));
            templateMap.put("votingPeriod", survey.takeVotingPeriod());

            return templateMap;
        }

        @Override
        public int compareTo(SurveyTemplated surveyTemplated) {
            Survey otherSurvey = surveyTemplated.survey;

            int compare = survey.getStartDate().compareTo(otherSurvey.getStartDate());

            if (compare == 0) {
                compare = survey.grabEndDate().compareTo(otherSurvey.grabEndDate());

                if (compare == 0) {
                    compare = survey.takeName().compareToIgnoreCase(otherSurvey.takeName());

                    if (compare == 0) {
                        compare = survey.obtainDescription().compareToIgnoreCase(otherSurvey.obtainDescription());
                    }
                }
            }

            return compare;
        }
    }
}
