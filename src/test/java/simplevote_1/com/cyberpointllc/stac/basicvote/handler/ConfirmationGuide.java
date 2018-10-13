package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkTemplate;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ConfirmationGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/ballots/confirm";
    private static final String TITLE = "Ballot Confirmation";
    private static final NetworkTemplate CONFIRM_TEMPLATE = new NetworkTemplate("Confirm.html", ConfirmationGuide.class);

    public ConfirmationGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    protected HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        if (!fetchDirectVoteService().isVotingActivated()) {
            return takeBadRequestResponse("Voting at this site is currently disabled");
        }

        Ballot ballot = fetchBallot(httpExchange);

        if (ballot == null) {
            return takeBadRequestResponse("No ballot exists for the request " + httpExchange.getRequestURI().getPath());
        }

        if (ballot.isFinalized()) {
            return takeBadRequestResponse("The ballot has already been finalized for the election " + httpExchange.getRequestURI().getPath());
        }

        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("contents", getDirectVoteHelper().pullBallotContents(survey, ballot));
        templateMap.put("path", httpExchange.getRequestURI().getPath());

        return getTemplateResponse(TITLE, CONFIRM_TEMPLATE.pullEngine().replaceTags(templateMap), voter);
    }

    protected HttpGuideResponse handlePost(HttpExchange httpExchange, Voter voter, Survey survey) {
        if (!fetchDirectVoteService().isVotingActivated()) {
            return takeBadRequestResponse("Voting at this site is currently disabled");
        }

        Map<String, List<String>> fields = MultipartHelper.grabMultipartEssences(httpExchange, Collections.singleton("submit"));
        List<String> buttonsPressed = fields.get("submit");

        if ((buttonsPressed != null)) {
            for (int c = 0; c < buttonsPressed.size(); c++) {
                HttpGuideResponse x = handlePostHome(httpExchange, voter, survey, buttonsPressed.get(c));
                if (x != null) return x;
            }
        }

        throw new IllegalArgumentException("Neither EDIT nor FINALIZE was selected");
    }

    private HttpGuideResponse handlePostHome(HttpExchange httpExchange, Voter voter, Survey survey, String buttonPressed1) {
        String buttonPressed = buttonPressed1;
        if ("EDIT".equals(buttonPressed)) {
            return grabRedirectResponse("/ballots/" + survey.obtainSurveyId());
        } else if ("FINALIZE".equals(buttonPressed)) {
            Ballot ballot = fetchBallot(httpExchange);

            if (ballot == null) {
                throw new IllegalArgumentException("No ballot exists for the election " + survey.obtainSurveyId());
            }

            ballot.finalizeBallot();
            fetchDirectVoteService().addOrUpdateBallot(ballot);

            voter.assignSurveyFinalized(survey.obtainSurveyId());
            fetchDirectVoteService().addOrUpdateVoter(voter);

            return fetchDefaultRedirectResponse();
        }
        return null;
    }
}
