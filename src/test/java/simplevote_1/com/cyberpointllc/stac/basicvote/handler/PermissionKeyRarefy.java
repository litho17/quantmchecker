package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.AbstractHttpGuide;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;

import java.io.IOException;

/**
 * Determines if the exchange is part of an existing active session
 * that also has an existing and valid registration key.
 * If so, the next item in the chain is called; otherwise, the
 * call is redirected to the registration key handler path.
 * The session property maps election id to registration key.
 */
public class PermissionKeyRarefy extends Filter {
    private final DirectVoteHelper directVoteHelper;
    private final String guideTrail;
    private final String permissionKeyGuideTrail;

    public PermissionKeyRarefy(DirectVoteHelper directVoteHelper,
                               String guideTrail,
                               String permissionKeyGuideTrail) {
        this.directVoteHelper = directVoteHelper;
        this.guideTrail = (guideTrail == null) ? "" : guideTrail.trim();

        if (permissionKeyGuideTrail == null) {
            permissionKeyGuideTrail = "/";
        } else {
            permissionKeyGuideTrail = permissionKeyGuideTrail.trim();

            if (!permissionKeyGuideTrail.endsWith("/")) {
                permissionKeyGuideTrail = permissionKeyGuideTrail + "/";
            }
        }

        this.permissionKeyGuideTrail = permissionKeyGuideTrail;
    }

    @Override
    public void doFilter(HttpExchange httpExchange, Filter.Chain chain) throws IOException {
        Survey survey = directVoteHelper.getSurvey(httpExchange, guideTrail);

        if (survey == null) {
            HttpGuideResponse response = AbstractHttpGuide.takeBadRequestResponse("No election exists for the request: " + httpExchange.getRequestURI().getPath());
            response.transmitResponse(httpExchange);
        } else {
            new PermissionKeyRarefyExecutor(httpExchange, chain, survey).invoke();
        }
    }

    @Override
    public String description() {
        return "Registration Key Filter";
    }

    private class PermissionKeyRarefyExecutor {
        private HttpExchange httpExchange;
        private Chain chain;
        private Survey survey;

        public PermissionKeyRarefyExecutor(HttpExchange httpExchange, Chain chain, Survey survey) {
            this.httpExchange = httpExchange;
            this.chain = chain;
            this.survey = survey;
        }

        public void invoke() throws IOException {
            directVoteHelper.assignPermissionTrail(httpExchange, httpExchange.getRequestURI().getPath());

            PermissionKey permissionKey = directVoteHelper.getPermissionKey(httpExchange, survey);

            if (permissionKey == null) {
                String trail = permissionKeyGuideTrail + survey.obtainSurveyId();
                HttpGuideResponse response = AbstractHttpGuide.grabRedirectResponse(trail);
                response.transmitResponse(httpExchange);
            } else {
                chain.doFilter(httpExchange);
            }
        }
    }
}
