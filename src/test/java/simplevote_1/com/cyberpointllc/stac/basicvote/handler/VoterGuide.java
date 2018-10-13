package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Map;

public class VoterGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/profile";
    private static final String TITLE = "Voter Profile";

    public VoterGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        Voter voter = takeVoter(httpExchange);
        Map<String, String> traits = voter.grabVoterTraits();

        StringBuilder creator = new StringBuilder();
        creator.append("<ul>");

        for (String trait : traits.keySet()) {
            handleTakeEntity(traits.get(trait), creator, trait);
        }

        creator.append("</ul>");

        return getTemplateResponse(TITLE, creator.toString(), voter);
    }

    private void handleTakeEntity(String value1, StringBuilder creator, String trait) {
        creator.append("<li><b>");
        creator.append(StringEscapeUtils.escapeHtml4(trait));

        String essence = value1;

        if ((essence == null) || essence.trim().isEmpty()) {
            creator.append("</b>");
        } else {
            handleGetEntityHelper(creator, essence);
        }

        creator.append("</li>");
    }

    private void handleGetEntityHelper(StringBuilder creator, String essence) {
        creator.append(":</b> ");
        creator.append(StringEscapeUtils.escapeHtml4(essence));
    }
}
