package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.util.Map;
import java.util.Set;

public interface StorageService {
    /**
     * Commit the database
     */
    void commit();

    /**
     * Commit then close the database
     */
    void close();

    /**
     * @return Set of elections
     */
    Set<Survey> obtainSurveys();

    /**
     * @return Set of questions
     */
    Set<Issue> takeIssues();

    /**
     * @return Set of choices ids
     */
    Set<String> takeChoiceIds();

    /**
     * @return Set of choices
     */
    Set<Choice> fetchSelections();

    /**
     * @return Set of voters
     */
    Set<Voter> obtainVoters();

    /**
     * @return Set of answers
     */
    Set<Reply> takeReplies();

    /**
     * @return Set of ballots
     */
    Set<Ballot> fetchBallots();

    /**
     * Returns the Election associated with the specified identity.
     *
     * @param surveyId used to look up the Election
     * @return Election matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Survey fetchSurvey(String surveyId);

    /**
     * Returns the Question associated with the specified identity.
     *
     * @param issueId used to look up the Question
     * @return Question matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Issue takeIssue(String issueId);

    /**
     * Returns the Choice associated with the specified identity.
     *
     * @param choiceId used to look up the Choice
     * @return Choice matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Choice takeChoice(String choiceId);

    /**
     * Returns the voter associated with the specified identity.
     *
     * @param voterId used to look up the voter
     * @return voter matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Voter grabVoter(String voterId);

    /**
     * Returns the answer associated with the specified identity.
     *
     * @param replyId used to look up the answer
     * @return answer matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Reply getReply(String replyId);

    /**
     * Returns the ballot associated with the specified identity.
     *
     * @param permissionKey used to look up the ballots
     * @param survey used to look up the ballots
     * @return ballot matching the id
     * will be <code>null</code> if no match exists
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Ballot pullBallot(PermissionKey permissionKey, Survey survey);

    /**
     * Returns all ballots associated with the specified election identity.
     *
     * @param surveyId used to look up matching ballots
     * @return Set of ballots matching the id;
     * may be empty but is guaranteed to not be <code>null</code>
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    Set<Ballot> takeBallots(String surveyId);

    /**
     * Returns the latest collected results (from all servers)
     * for the specified election id.
     *
     * @param surveyId used to look up the latest results
     * @return ElectionResults for the election Id;
     * may be <code>null</code> if no results are associated with the election
     */
    SurveyOutcomes fetchAccruedSurveyOutcomes(String surveyId);

    /**
     * Each election has a set of registration keys,
     * each of which is associated with a voter
     * and, ultimately, a ballot.
     * This returns a map of voter ids to
     * registration keys for the given election id.
     * If no voters are associated with the specified
     * election, an empty map will be returned.
     *
     * @param surveyId used to look up the map of voter ids to
     *                   registration keys
     * @return Map of voter ids to registration keys;
     * may be empty but guaranteed to not be <code>null</code>
     */
    Map<String, PermissionKey> pullPermissionKeysForSurvey(String surveyId);

    /**
     * Adds or updates the specified election to the collection of elections.
     *
     * @param survey the election to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateSurvey(Survey survey);

    /**
     * Adds or updates the specified question to the collection of questions.
     *
     * @param issue the question to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateIssue(Issue issue);

    /**
     * Adds or updates the specified choice to the collection of choices.
     *
     * @param choice the choice to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateChoice(Choice choice);

    /**
     * Adds or updates the specified voter to the collection of voters.
     *
     * @param voter the voter to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateVoter(Voter voter);

    /**
     * Adds or updates the specified answer to the collection of answers.
     *
     * @param reply the answer to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateReply(Reply reply);

    /**
     * Adds or updates the specified ballot to the collection of ballots.
     *
     * @param ballot the ballot to be added
     * @return boolean true if successfully modified
     * @throws IllegalArgumentException if argument is <code>null</code>
     */
    boolean addOrUpdateBallot(Ballot ballot);

    /**
     * Adds or updates the results of a particular election, accrued from all servers
     *
     * @param accruedOutcomes the most recent results in an election from all servers
     * @return boolean true if modified
     */
    boolean addOrUpdateOutcomes(SurveyOutcomes accruedOutcomes);

    /**
     * Removes the election with the specified id from the collection of elections.
     *
     * @param surveyId id of the election to delete
     * @return boolean true if election removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteSurvey(String surveyId);

    /**
     * Removes the question with the specified id from the collection of questions.
     *
     * @param issueId id of the question to delete
     * @return boolean true if question removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteIssue(String issueId);

    /**
     * Removes the choice with the specified id from the collection of choices.
     *
     * @param choiceId id of the choice to delete
     * @return boolean true if choice removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteChoice(String choiceId);

    /**
     * Removes the voter with the specified id from the collection of voters.
     *
     * @param voterId id of the voter to delete
     * @return boolean true if voter removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteVoter(String voterId);

    /**
     * Removes the answer with the specified id from the collection of answers.
     *
     * @param replyId id of the answer to delete
     * @return boolean true if answer removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteReply(String replyId);

    /**
     * Removes the ballot with the specified id from the collection of ballots.
     *
     * @param ballotId id of the ballot to delete
     * @return boolean true if ballot removed
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    boolean deleteBallot(String ballotId);

    /**
     * Adds a question with an id to the database.
     * Does not allow a duplicate ID in the database
     *
     * @param issue to add to the database
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    void addIssue(Issue issue);

    /**
     * Adds a choice with an id to the database.
     * Does not allow a duplicate ID in the database
     *
     * @param choice to add to the database
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    void addChoice(Choice choice);

    /**
     * Adds a voter with an id to the database.
     * Does not allow a duplicate ID in the database
     *
     * @param voter to add to the database
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    void addVoter(Voter voter);

    /**
     * Adds a answer with an id to the database.
     * Does not allow a duplicate ID in the database
     *
     * @param reply to add to the database
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    void addReply(Reply reply);

    /**
     * Adds a ballot with an id to the database.
     * Does not allow a duplicate ID in the database
     *
     * @param ballot to add to the database
     * @throws IllegalArgumentException if argument is <code>null</code> or empty
     */
    void addBallot(Ballot ballot);

    /**
     * Adds the registration key associated with the
     * specified voter id and election id.
     *
     * @param permissionKey to be bound to the voter and election
     * @param surveyId      bound to the registration key
     * @param voterId         bound to the registration key
     */
    void addPermissionKey(PermissionKey permissionKey, String surveyId, String voterId);

    /**
     * Summarizes the data in the database
     *
     * @return String with summary
     */
    String summary();

    /**
     *
     * Prunes Database entries that should not exist
     */
    void cleanDatabase();

    /**
     * Create a ballotId
     * @param permissionKey for a ballot
     * @param surveyId for a ballot
     * @return encrypted string of the registrationKey and electionId
     */
    String formBallotId(String permissionKey, String surveyId);

    /**
     * Create an answerId
     * @param ballotId for an answer
     * @param issueId for an answer
     * @return encrypted string of the ballotId and questionId
     */
    String formReplyId(String ballotId, String issueId);

    /**
     * Create a questionId
     * @param surveyId for a Question
     * @return a unique id for a Question
     */
    String formIssueId(String surveyId);

    /**
     * Create a choiceId
     * @param surveyId for a Choice
     * @param issueId for a Choice
     * @return a unique id for a Choice
     */
    String formChoiceId(String surveyId, String issueId);

    /**
     * Create an electionId
     * @return a unique id for an Election
     */
    String formSurveyId();
}
