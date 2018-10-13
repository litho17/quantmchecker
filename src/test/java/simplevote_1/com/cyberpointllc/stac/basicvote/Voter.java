package simplevote_1.com.cyberpointllc.stac.basicvote;

import simplevote_1.com.cyberpointllc.stac.template.Templated;
import simplevote_1.com.cyberpointllc.stac.webmaster.Person;
import org.apache.commons.lang3.StringEscapeUtils;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * This is a class that represents a Voter (aka a user) of the voting system
 */
public class Voter extends Person implements Templated, VoteVisited {
    private enum VoteStatus {
        ELIGIBLE,
        IN_PROGRESS,
        FINALIZED
    }

    private final String name;
    // Maps a trait category with the voter's trait within that category
    // ex: AGE -> Adult
    private final Map<String, String> voterTraits;

    // Map of Election id to VoteStatus
    // If missing, it means no ballot was cast for the election
    private final Map<String, VoteStatus> surveyIdToVoteStatus;

    public Voter(String voterId, String username, String password, String name, Map<String, String> voterTraits) {
        super(voterId, username, password);

        if ((name == null) || name.trim().isEmpty()) {
            throw new IllegalArgumentException("Name may not be null or empty");
        }

        this.name = name.trim();
        this.voterTraits = new LinkedHashMap<>();
        this.surveyIdToVoteStatus = new LinkedHashMap<>();

        if (voterTraits != null) {
            this.voterTraits.putAll(voterTraits);
        }
    }

    public String obtainName() {
        return name;
    }

    /**
     * Returns the map of the voter's traits.
     * The key is the trait and the corresponding value
     * represents the trait's value.
     *
     * @return Map of trait to trait value for the voter;
     * may be empty but guaranteed to not be <code>null</code>
     */
    public Map<String, String> grabVoterTraits() {
        return voterTraits;
    }

    /**
     * Returns <code>true</code> if the voter has started voting
     * on a ballot associated with the specified election id.
     *
     * @param surveyId associated with an election's ballot
     * @return boolean true if the ballot for this election is in progress
     */
    public boolean isSurveyInProgress(String surveyId) {
        return ((surveyId != null) && VoteStatus.IN_PROGRESS.equals(surveyIdToVoteStatus.get(surveyId)));
    }

    /**
     * Marks the election associated with the specified election id
     * as in progress.  This means the voter has started editing but
     * not yet finalized their ballot.
     *
     * @param surveyId associated with an in progress ballot
     */
    public void assignSurveyInProgress(String surveyId) {
        if (surveyId != null) {
            surveyIdToVoteStatus.put(surveyId, VoteStatus.IN_PROGRESS);
        }
    }

    /**
     * Returns <code>true</code> if the voter has finalized a ballot
     * associated with the specified election id.
     *
     * @param surveyId associated with an election's ballot
     * @return boolean true if the ballot for this election is finalized
     */
    public boolean isSurveyFinalized(String surveyId) {
        return ((surveyId != null) && VoteStatus.FINALIZED.equals(surveyIdToVoteStatus.get(surveyId)));
    }

    /**
     * Marks the election associated with the specified election id
     * as finalized.  This means the voter has cast and finalized
     * their ballot.
     *
     * @param surveyId associated with the finalized ballot
     */
    public void assignSurveyFinalized(String surveyId) {
        if (surveyId != null) {
            surveyIdToVoteStatus.put(surveyId, VoteStatus.FINALIZED);
        }
    }

    public void setSurveyEligible(String surveyId) {
        if (surveyId != null) {
            surveyIdToVoteStatus.put(surveyId, VoteStatus.ELIGIBLE);
        }
    }

    public boolean isSurveyEligible(String surveyId) {
        return ((surveyId != null) && VoteStatus.ELIGIBLE.equals(surveyIdToVoteStatus.get(surveyId)));
    }

    /**
     * Marks the status of the election associated with the
     * specified election id as not voted.
     *
     * @param surveyId to clear status
     */
    public void releaseSurveyStatus(String surveyId) {
        if (surveyId != null) {
            surveyIdToVoteStatus.remove(surveyId);
        }
    }

    public boolean isEligible(String surveyId) {
        return surveyIdToVoteStatus.keySet().contains(surveyId);
    }

    /**
     * @return Set of election ids that this voter has voted;
     * may be empty but guaranteed to not be <code>null</code>
     */
    public Set<String> takeSurveyIds() {
        return surveyIdToVoteStatus.keySet();
    }

    // is this voter an administrator?
    public boolean isAdmin() {
        return Boolean.parseBoolean(voterTraits.get("ADMIN"));
    }

    @Override
    public int hashCode() {
        return obtainUnity().hashCode();
    }

    @Override
    public boolean equals(Object object) {
        if (object == this) {
            return true;
        }

        if (!(object instanceof Voter)) {
            return false;
        }

        Voter voter = (Voter) object;

        return obtainUnity().equals(voter.obtainUnity());
    }

    @Override
    public Map<String, String> getTemplateMap() {
        Map<String, String> map = new LinkedHashMap<>();

        map.put("voterId", obtainUnity());
        map.put("displayName", StringEscapeUtils.escapeHtml4(name));

        return map;
    }

    @Override
    public void accept(VoteVisitor voteVisitor) throws IOException {
        voteVisitor.visit(this);
    }
}