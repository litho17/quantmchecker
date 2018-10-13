package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKeyCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionAuthenticator;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.HttpGuideResponse;
import simplevote_1.com.cyberpointllc.stac.webmaster.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class PermissionAssessGuide extends AbstractDirectVoteGuide {
    private static final String TRAIL = "/registrationkey";
    private static final String TITLE = "Registration Key Verification";
    private static final String PERMISSION_KEY_FIELD = "regkey";
    private static final String ERROR_KEY = "REGISTRATION@KEY@CHECK@";

    private PermissionAuthenticator authenticator;

    private enum Outcome {
        OKAY("", ""),
        NOT_AUTHORIZED("authorized", "<p style=\"color:red\">Key is not authorized in the selected election.</p>"),
        INVALID("invalid", "<p style=\"color:red\">Registration key is invalid.</p>"),
        EMPTY("empty", "<p style=\"color:red\">A non-empty registration key must be specified.</p>");

        private final String keyword;
        private final String message;

        Outcome(String keyword, String message) {
            this.keyword = keyword;
            this.message = message;
        }

        public static Outcome fromKeyword(String keyword) {
            if (keyword != null) {
                Outcome[] essences = values();
                for (int a = 0; a < essences.length; a++) {
                    Outcome outcome = essences[a];
                    if (outcome.keyword.equalsIgnoreCase(keyword)) {
                        return outcome;
                    }
                }
            }

            return OKAY;
        }
    }

    private static final TemplateEngine FORM_TEMPLATE = new TemplateEngine("{{errorMessage}}<br>\n" +
            "<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">\n" +
            "    RegistrationKey: <input type=\"password\" name=\"regkey\" placeholder=\"Enter your registration key\"/><br/>\n" +
            "    <input type=\"submit\" value=\"Submit\" name=\"submit\"/>\n" +
            "</form>"
    );

    public PermissionAssessGuide(DirectVoteHelper directVoteHelper) {
        super(directVoteHelper);
        authenticator = new PermissionAuthenticator(directVoteHelper.pullDirectVoteService());
    }

    @Override
    public String takeTrail() {
        return TRAIL;
    }

    @Override
    protected HttpGuideResponse handleFetch(HttpExchange httpExchange, Voter voter, Survey survey) {
        Map<String, String> templateMap = new HashMap<>();
        templateMap.put("path", httpExchange.getRequestURI().getPath());

        Outcome outcome = Outcome.fromKeyword(getDirectVoteHelper().obtainSessionProperty(httpExchange, ERROR_KEY + survey.obtainSurveyId()));
        templateMap.put("errorMessage", outcome.message);

        return getTemplateResponse(TITLE, FORM_TEMPLATE.replaceTags(templateMap), voter);
    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange, Voter voter, Survey survey) {
        Set<String> fieldNames = Collections.singleton(PERMISSION_KEY_FIELD);
        Map<String, List<String>> fields = MultipartHelper.grabMultipartEssences(httpExchange, fieldNames);
        List<String> permissionKeys = fields.get(PERMISSION_KEY_FIELD);

        Outcome outcome = Outcome.EMPTY;

        if ((permissionKeys != null) && (permissionKeys.size() == 1)) {
            String key = permissionKeys.get(0);

            if ((key != null) && !key.trim().isEmpty()) {
                key = key.trim();

                if (authenticator.confirm(key)) {
                    if (fetchDirectVoteService().confirmPermissionKey(survey, voter, new PermissionKeyCreator().setKey(key).formPermissionKey())) {
                        getDirectVoteHelper().definePermissionKey(httpExchange, survey, key);
                        outcome = Outcome.OKAY;
                    } else {
                        outcome = Outcome.NOT_AUTHORIZED;
                    }
                } else {
                    outcome = Outcome.INVALID;
                }
            }
        }

        HttpGuideResponse response;

        getDirectVoteHelper().defineSessionProperty(httpExchange, ERROR_KEY + survey.obtainSurveyId(), outcome.keyword);

        if (Outcome.OKAY.equals(outcome)) {
            String trail = getDirectVoteHelper().fetchPermissionTrail(httpExchange);

            if (trail != null) {
                response = grabRedirectResponse(trail);
            } else {
                response = fetchDefaultRedirectResponse();
            }
        } else {
            // Failure; return to this page but include an error message
            response = grabRedirectResponse(httpExchange.getRequestURI().getPath());
        }

        return response;
    }
}
