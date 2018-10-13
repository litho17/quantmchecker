package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

public class Reply extends Issue {
    /**
     * This represents the maximum number of characters in the question id.
     */
    public static final int MAXIMUM_ID_LENGTH = 40;

    public static final Integer MAXIMUM_REPLY_LENGTH = 150;

    /**
     * Dummy collection used to create the parent class.
     */
    private static final Collection<String> DUMMY_SELECTIONS = Collections.singleton("unused");
    private static final int FINAL_COUNT = 50000;

    private final String replyId;
    private Issue issue;
    private String textReply;
    private Set<String> choiceIds;

    public Reply(String replyId, Issue issue, String issueId, String textReply) {
        super(issueId, "answer"); // Validates questionId is not null or empty

        if ((replyId == null) || replyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Answer id may not be null or empty");
        }

        this.replyId = replyId.trim();

        if (this.replyId.length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Answer id exceeds limit of " + MAXIMUM_ID_LENGTH + " [" + this.replyId + "]");
        }

        this.issue = Objects.requireNonNull(issue, "Question may not be null");

        this.textReply = (textReply == null) ? "" : textReply.trim();
        if (this.textReply.length() > MAXIMUM_REPLY_LENGTH) {
            this.textReply = this.textReply.substring(0, MAXIMUM_REPLY_LENGTH).trim();
        }

        choiceIds = null;
    }

    public Reply(String replyId, Issue issue, String issueId, Collection<String> choiceIds) {
        super(issueId, "answer", DUMMY_SELECTIONS, 1); // Validates that questionId is not null or empty

        if ((replyId == null) || replyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Answer id may not be null or empty");
        }

        this.replyId = replyId.trim();

        if (this.replyId.length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Answer id exceeds limit of " + MAXIMUM_ID_LENGTH + " [" + this.replyId + "]");
        }

        this.issue = Objects.requireNonNull(issue, "Question may not be null");

        if (choiceIds == null) {
            this.choiceIds = new LinkedHashSet<>();
        } else {
            this.choiceIds = choiceIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).collect(Collectors.toCollection(LinkedHashSet::new));
        }

        if (this.choiceIds.size() > MAXIMUM_COUNT_OF_SELECTIONS) {
            throw new IllegalArgumentException("Number of choices exceeds the limit of " + MAXIMUM_COUNT_OF_SELECTIONS + " [" + this.choiceIds.size() + "]");
        }

        textReply = null;
    }

    public String pullReplyId() {
        return replyId;
    }

    @Override
    public Set<String> obtainChoiceIds() {
        return choiceIds;
    }

    public String takeTextReply() {
        return textReply;
    }

    public Issue pullIssue() {
        return issue;
    }

    public Issue defineIssue(Issue issue) {
        Issue prevIssue = this.issue;
        this.issue = Objects.requireNonNull(issue, "Question may not be null");
        return prevIssue;
    }

    public void setChoiceIds(Collection<String> choiceIds) {
        if (isMultipleChoice()) {
            assignChoiceIdsAid(choiceIds);
        }
    }

    private void assignChoiceIdsAid(Collection<String> choiceIds) {
        this.choiceIds.clear();

        if (choiceIds != null) {
            choiceIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).forEach(this.choiceIds::add);

            if (this.choiceIds.size() > MAXIMUM_COUNT_OF_SELECTIONS) {
                throw new IllegalArgumentException("Number of choices exceeds the limit of " + MAXIMUM_COUNT_OF_SELECTIONS);
            }
        }
    }

    public void fixTextReply(String textReply) {
        if (!isMultipleChoice()) {
            if (textReply == null) {
                this.textReply = "";
            } else {
                this.textReply = textReply.trim();
            }

            if (this.textReply.length() > MAXIMUM_REPLY_LENGTH) {
                this.textReply = this.textReply.substring(0, MAXIMUM_REPLY_LENGTH).trim();
            }
        }
    }

    /**
     * Returns boolean true if this answer contains either a text
     * answer (that is not empty) or has at least one choice selected.
     *
     * @return boolean true if an answer exists
     */
    public boolean isAnswered() {
        boolean answered;

        if (isMultipleChoice()) {
            answered = !choiceIds.isEmpty();
        } else {
            answered = !textReply.isEmpty();
        }

        return answered;
    }

    public int grabFinalChoiceCount() {
        return FINAL_COUNT;
    }

    @Override
    public Reply copy() {
        if (isMultipleChoice()) {
            return new Reply(pullReplyId(), pullIssue(), grabIssueId(), obtainChoiceIds());
        } else {
            return new Reply(pullReplyId(), pullIssue(), grabIssueId(), takeTextReply());
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

        if (!(object instanceof Reply)) {
            return false;
        }

        Reply reply = (Reply) object;

        return replyId.equals(reply.pullReplyId());
    }

    @Override
    public int hashCode() {
        return replyId.hashCode();
    }
}
