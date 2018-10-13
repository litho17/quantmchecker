package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This is a class that brings together the questions and the choices in order for the Voter to cast their vote
 */
public class Ballot implements VoteVisited {
    /**
     * This represents the maximum number of characters in the ballot id.
     */
    public static final int MAXIMUM_ID_LENGTH = 40;

    private final String ballotId;
    private final PermissionKey permissionKey;
    private final String surveyId;

    private final Set<String> replyIds;

    private boolean isFinalized;

    public Ballot(String ballotId, PermissionKey permissionKey, String surveyId) {
        this(ballotId, permissionKey, surveyId, Collections.<String>emptySet(), false);
    }

    public Ballot(String ballotId, PermissionKey permissionKey, String surveyId, Set<String> replyIds, boolean isFinalized) {
        if ((ballotId == null) || ballotId.trim().isEmpty()) {
            throw new IllegalArgumentException("Ballot id may not be null or empty");
        }

        if (ballotId.trim().length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Ballot id length exceeds limit of " + MAXIMUM_ID_LENGTH + " [" + ballotId + "]");
        }

        this.ballotId = ballotId.trim();

        if (permissionKey == null) {
            throw new IllegalArgumentException("Registration key may not be null");
        }

        this.permissionKey = permissionKey;

        if ((surveyId == null) || surveyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Election id may not be null or empty");
        }

        if (surveyId.trim().length() > Survey.MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Election id length exceeds limit of " + Survey.MAXIMUM_ID_LENGTH + " [" + surveyId + "]");
        }

        this.surveyId = surveyId.trim();

        if ((replyIds == null) || replyIds.isEmpty()) {
            this.replyIds = new LinkedHashSet<>();
        } else {
            this.replyIds = replyIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).collect(Collectors.toCollection(LinkedHashSet::new));
        }

        this.isFinalized = isFinalized;
    }

    public String pullBallotId() {
        return ballotId;
    }

    public PermissionKey takePermissionKey() {
        return permissionKey;
    }

    public String pullSurveyId() {
        return surveyId;
    }

    public Set<String> obtainReplies() {
        return replyIds;
    }

    public boolean isFinalized() {
        return isFinalized;
    }

    public void finalizeBallot() {
        isFinalized = true;
    }

    public void assignReplies(Set<String> replyIds) {
        if (isFinalized()) {
            throw new IllegalStateException("Cannot set answers on a finalized ballot");
        }

        this.replyIds.clear();

        if (replyIds != null) {
            replyIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).forEach(this.replyIds::add);
        }
    }

    @Override
    public void accept(VoteVisitor voteVisitor) throws IOException {
        voteVisitor.visit(this);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Ballot)) {
            return false;
        }

        Ballot ballot = (Ballot) object;

        return ballotId.equals(ballot.pullBallotId());
    }

    @Override
    public int hashCode() {
        return ballotId.hashCode();
    }
}
