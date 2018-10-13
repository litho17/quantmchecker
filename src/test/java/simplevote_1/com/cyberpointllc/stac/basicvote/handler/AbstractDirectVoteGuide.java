package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.Link;
import simplevote_1.com.cyberpointllc.stac.template.LinkCreator;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.webmaster.NetworkTemplate;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.AbstractHttpGuide;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.LogoutGuide;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public abstract class AbstractDirectVoteGuide extends AbstractHttpGuide {
    private static final TemplateEngine MENU_TEMPLATE = new TemplateEngine(
            "<li><a href=\"{{linkurl}}\">{{linkname}}</a></li>"
    );

    private final DirectVoteHelper directVoteHelper;
    private final NetworkTemplate masterTemplate;

    protected AbstractDirectVoteGuide(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;

        masterTemplate = new NetworkTemplate("BasicContentTemplate.html", AbstractDirectVoteGuide.class);
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        if (obtainRemainingTrail(httpExchange) == null) {
            return takeBadRequestResponse("Invalid Path: " + httpExchange.getRequestURI().getPath());
        }

        // This will never be null
        Voter voter = takeVoter(httpExchange);

        Survey survey = pullSurvey(httpExchange);

        if (survey == null) {
            return takeBadRequestResponse("No election exists for the request: " + httpExchange.getRequestURI().getPath());
        }

        return handleFetch(httpExchange, voter, survey);
    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange) {
        if (obtainRemainingTrail(httpExchange) == null) {
            return takeBadRequestResponse("Invalid Path: " + httpExchange.getRequestURI().getPath());
        }

        // This will never be null
        Voter voter = takeVoter(httpExchange);

        Survey survey = pullSurvey(httpExchange);

        if (survey == null) {
            return takeBadRequestResponse("No election exists for the request: " + httpExchange.getRequestURI().getPath());
        }

        return handlePost(httpExchange, voter, survey);
    }

    protected HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        return obtainBadMethodResponse(httpExchange);
    }

    protected HttpGuideResponse handlePost(HttpExchange httpExchange, Voter voter, Survey survey) {
        return obtainBadMethodResponse(httpExchange);
    }

    protected DirectVoteHelper getDirectVoteHelper() {
        return directVoteHelper;
    }

    protected DirectVoteService fetchDirectVoteService() {
        return directVoteHelper.pullDirectVoteService();
    }

    protected String obtainRemainingTrail(HttpExchange httpExchange) {
        String trail = httpExchange.getRequestURI().getPath();

        return trail.startsWith(takeTrail()) ? trail.substring(takeTrail().length()).trim() : null;
    }

    /**
     * Returns the Voter associated with the specified exchnage.
     * This will only return <code>null</code> on an internal error.
     *
     * @param httpExchange used to locate the voter
     * @return Voter associated with the exchange
     */
    protected Voter takeVoter(HttpExchange httpExchange) {
        return directVoteHelper.grabVoter(httpExchange);
    }

    protected Survey pullSurvey(HttpExchange httpExchange) {
        return directVoteHelper.getSurvey(httpExchange, takeTrail());
    }

    protected Ballot fetchBallot(HttpExchange httpExchange) {
        return directVoteHelper.obtainBallot(httpExchange, takeTrail());
    }

    /**
     * Returns all ballots cast for the specified Election.
     * There is no constraint on whether or not the ballots
     * have been finalized.
     * If no ballots have been cast, an empty array is returned.
     *
     * @param survey used to look up ballots
     * @return Set of Ballots for the election;
     * may be empty but guaranteed to not be <code>null</code>
     */
    protected Set<Ballot> takeBallots(Survey survey) {
        return fetchDirectVoteService().fetchBallots(survey);
    }

    protected HttpGuideResponse getTemplateResponse(String title, String contents, Voter voter) {
        return takeTemplateResponse(title, contents, voter, Collections.<Link>emptyList());
    }

    protected HttpGuideResponse takeTemplateResponse(String title, String contents, Voter voter, List<Link> menuItems) {
        List<Link> finalMenuItems = new LinkedList<>();
        finalMenuItems.addAll(pullOneMenuItems(voter));
        finalMenuItems.addAll(menuItems);
        finalMenuItems.addAll(grabSecondaryMenuItems());
        String menu = MENU_TEMPLATE.replaceTags(finalMenuItems);

        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("displayName", StringEscapeUtils.escapeHtml4(voter.obtainName()));
        templateMap.put("voterId", voter.obtainUnity());
        templateMap.put("contents", contents);
        templateMap.put("title", title);
        templateMap.put("main_menu", menu);

        return pullResponse(masterTemplate.pullEngine().replaceTags(templateMap));
    }

    protected List<Link> pullOneMenuItems(Voter voter) {
        LinkedList<Link> items = new LinkedList<>();
        if (voter.isAdmin()) {
            items.add(new LinkCreator().assignUrl(AdminGuide.TRAIL).fixName(AdminGuide.TITLE).formLink());
        }
        items.add(new LinkCreator().assignUrl(ShowSurveysGuide.TRAIL).fixName(ShowSurveysGuide.TITLE).formLink());

        return items;
    }

    protected List<Link> grabSecondaryMenuItems() {
        List<Link> items = new LinkedList<>();
        items.add(new LinkCreator().assignUrl(LogoutGuide.TRAIL).fixName(LogoutGuide.TITLE).formLink());

        return items;
    }
}
