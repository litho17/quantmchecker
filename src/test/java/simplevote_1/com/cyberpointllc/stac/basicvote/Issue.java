package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This is one of the items contained on the Ballot.
 * The voters cycle through questions and select choices
 * in order to vote in the election
 */
public class Issue implements VoteVisited {
    /**
     * This represents the maximum number of characters in the question id.
     */
    public static final int MAXIMUM_ID_LENGTH = 10;

    /**
     * This represents the maximum number of characters in the question text.
     */
    public static final int MAXIMUM_ISSUE_TEXT_LENGTH = 80;

    /**
     * This represents the maximum number of choices permitted for a question.
     * Furthermore, it indicates the maximum number of unique free responses.
     */
    public static final int MAXIMUM_COUNT_OF_SELECTIONS = 20;

    private static Map<String, Integer> numTimesSerialized = new HashMap<>();

    // There are three types of questions: free response, check box questions, and radio button questions
    private enum Type {
        TEXT_RESPONSE, ASSESS_BOX, RADIO_BUTTON
    }

    private final String issueId;
    private final String text; // May contain HTML
    private final Set<String> choiceIds;
    private final int maxSelections;
    private final Type type;

    /**
     * This constructor makes either CHECK_BOX questions or RADIO_BUTTON questions.
     * If maxChoices > 1, it makes a CHECK_BOX question.
     *
     * @param issueId unique id of this question
     * @param text       representing the question to be asked
     * @param choiceIds  that represent the possible answer choices
     * @param maxSelections the greatest number of selected choices
     */
    public Issue(String issueId, String text, Collection<String> choiceIds, int maxSelections) {
        if ((issueId == null) || issueId.trim().isEmpty()) {
            throw new IllegalArgumentException("Question ID may not be null or empty");
        }

        this.issueId = issueId.trim();

        if (this.issueId.length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Question id exceeds limit of " + MAXIMUM_ID_LENGTH + " [" + this.issueId + "]");
        }

        if ((text == null) || text.trim().isEmpty()) {
            throw new IllegalArgumentException("Question text may not be null or empty");
        }

        this.text = text.trim();

        if (this.text.length() > MAXIMUM_ISSUE_TEXT_LENGTH) {
            throw new IllegalArgumentException("Question text exceeds limit of " + MAXIMUM_ISSUE_TEXT_LENGTH + " [" + this.text + "]");
        }

        if ((choiceIds == null) || choiceIds.isEmpty()) {
            throw new IllegalArgumentException("Question choices may not be null or empty");
        }

        this.choiceIds = choiceIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).collect(Collectors.toCollection(LinkedHashSet::new));

        if (this.choiceIds.isEmpty()) {
            throw new IllegalArgumentException("Question choices may not be empty");
        }

        if (this.choiceIds.size() > MAXIMUM_COUNT_OF_SELECTIONS) {
            throw new IllegalArgumentException("Number of choices exceeds the limit of " + MAXIMUM_COUNT_OF_SELECTIONS + " [" + choiceIds.size() + "]");
        }

        this.maxSelections = maxSelections < 1 ? 1 : Math.min(maxSelections, this.choiceIds.size());

        // maxChoices specifies the number of choices a voter can select for this question
        // if the maxChoices is greater than one, this question must be a check box question
        type = (this.maxSelections > 1) ? Type.ASSESS_BOX : Type.RADIO_BUTTON;
    }

    /**
     * This is a free response question.
     *
     * @param issueId unique id of this question
     * @param text       representing the question to be asked
     */
    public Issue(String issueId, String text) {
        if ((issueId == null) || issueId.trim().isEmpty()) {
            throw new IllegalArgumentException("Question ID may not be null or empty");
        }

        this.issueId = issueId.trim();

        if (this.issueId.length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Question id exceeds limit of " + MAXIMUM_ID_LENGTH);
        }

        if ((text == null) || text.trim().isEmpty()) {
            throw new IllegalArgumentException("Question text may not be null or empty");
        }

        this.text = text.trim();

        if (this.text.length() > MAXIMUM_ISSUE_TEXT_LENGTH) {
            throw new IllegalArgumentException("Question text exceeds limit of " + MAXIMUM_ISSUE_TEXT_LENGTH);
        }

        choiceIds = null;
        maxSelections = -1;
        type = Type.TEXT_RESPONSE;
    }

    public String grabIssueId() {
        return issueId;
    }

    public String pullText() {
        return text;
    }

    public int fetchMaxSelections() {
        return maxSelections;
    }

    public Set<String> obtainChoiceIds() {
        return choiceIds;
    }

    public boolean isMultipleChoice() {
        return ((type == Type.ASSESS_BOX) || (type == Type.RADIO_BUTTON));
    }

    public Issue copy() {
        if (isMultipleChoice()) {
            return new Issue(issueId, text, choiceIds, maxSelections);
        } else {
            return new Issue(issueId, text);
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

        if (!(object instanceof Issue)) {
            return false;
        }

        Issue issue = (Issue) object;

        return issueId.equals(issue.grabIssueId());
    }

    @Override
    public int hashCode() {
        return issueId.hashCode();
    }
}
