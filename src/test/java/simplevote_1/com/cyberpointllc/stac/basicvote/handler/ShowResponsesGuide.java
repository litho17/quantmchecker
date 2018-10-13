package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;

import java.util.HashMap;
import java.util.Map;

public class ShowResponsesGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/ballots/responses";
    private static final String TITLE = "Past Election Responses";

    private static final TemplateEngine RESPONSE_TEMPLATE = new TemplateEngine(
            "<strong>The following {{header}} for this election.</strong><br>{{contents}}"
    );

    public ShowResponsesGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    protected HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        Ballot ballot = fetchBallot(httpExchange);

        // If the ballot is null, it means no ballot was cast.
        String contents = getDirectVoteHelper().pullBallotContents(survey, ballot);
        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("header", (ballot == null) ? "were the questions" : "were the responses you entered");
        templateMap.put("contents", contents);
        return getTemplateResponse(TITLE, RESPONSE_TEMPLATE.replaceTags(templateMap), voter);
    }
}
