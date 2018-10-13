package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;

/**
 * A choice is a potential response to a Question.
 * The choice is set as an answer when it is selected on the ballot.
 */
public class Choice implements VoteVisited {
    /**
     * This represents the maximum number of characters in the choice id.
     */
    public static final int MAXIMUM_ID_LENGTH = 10;

    /**
     * This represents the maximum number of characters in the choice value.
     */
    public static final int MAXIMUM_CHOICE_ESSENCE_LENGTH = 80;

    private final String choiceId;
    private final String choiceEssence;

    public Choice(String choiceId, String choiceEssence) {
        if ((choiceId == null) || choiceId.trim().isEmpty()) {
            throw new IllegalArgumentException("Choice id may not be null or empty");
        }

        if (choiceId.trim().length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Choice id length exceeds the limit of " + MAXIMUM_ID_LENGTH + " [" + choiceId + "]");
        }

        if ((choiceEssence == null) || choiceEssence.trim().isEmpty()) {
            throw new IllegalArgumentException("Choice value may not be null or empty");
        }

        if (choiceEssence.trim().length() > MAXIMUM_CHOICE_ESSENCE_LENGTH) {
            throw new IllegalArgumentException("Choice value length exceeds the limit of " + MAXIMUM_CHOICE_ESSENCE_LENGTH + " [" + choiceEssence + "]");
        }

        this.choiceId = choiceId.trim();
        this.choiceEssence = choiceEssence.trim();
    }

    public String getChoiceEssence() {
        return choiceEssence;
    }

    public String pullChoiceId() {
        return choiceId;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Choice)) {
            return false;
        }

        Choice choice = (Choice) object;
        return choiceId.equals(choice.pullChoiceId());
    }

    @Override
    public int hashCode() {
        return choiceId.hashCode();
    }

    @Override
    public void accept(VoteVisitor voteVisitor) throws IOException {
        voteVisitor.visit(this);
    }
}
