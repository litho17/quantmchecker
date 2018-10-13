package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.util.List;
import java.util.Set;

/**
 * This is an interface that handles all of the voting functionality.
 */
public interface DirectVoteService {
    /**
     * Identifier used to indicate when a question is not answered
     */
    String DID_NOT_VOTE_ID = "Not Voted";

    /**
     * @return boolean true if voting with this service is enabled
     */
    boolean isVotingActivated();

    /**
     * Allow an admin user to enable or disable voting.
     *
     * @param activated boolean true if voting should be enabled
     */
    void fixVotingActivated(boolean activated);

    /**
     * @param voterId used to look up voter
     * @return Voter from id
     */
    Voter pullVoter(String voterId);

    /**
     * @return Set of all Voters
     */
    Set<Voter> fetchVoters();

    /**
     * @return Set of all Election
     */
    Set<Survey> pullSurveys();

    /**
     * Gets the election object associated with the given election id.
     */
    Survey fetchSurvey(String surveyId);

    /**
     * Get the questions for a given election.
     *
     * @param survey used to look up questions
     * @return Set of Questions associated with an election
     */
    Set<Issue> obtainIssues(Survey survey);

    /**
     * Get the question associated with the given question id.
     *
     * @param issueId used to look up the question
     * @return Question matching the id
     */
    Issue takeIssue(String issueId);

    /**
     * Gets a set of all choices associated with the given question.
     *
     * @param issue used to look up choices
     * @return Set of Choices associated with the question
     */
    Set<Choice> getSelections(Issue issue);

    /**
     * Get the choice associated with the given choice id.
     *
     * @param choiceId used to look up the choice
     * @return Choice matching the id
     */
    Choice pullChoice(String choiceId);

    /**
     * Get the eligible voters for election.
     *
     * @param electionid election id
     * @return Set of Voters that can vote in this election
     */
    Set<Voter> pullEligibleVoters(String electionid);

    /**
     * Count the eligible voters for election.
     *
     * @param electionid election id
     * @return number of voters registered for this election
     */
    int countEligibleVoters(String electionid);

    /**
     * Count how many voters submitted a ballot in this election.
     *
     * @param surveyId used to look up ballots
     * @return int representing the number of participating voters
     */
    int countParticipatingVoters(String surveyId);

    /**
     * Gets the answer associated with the given answer id.
     *
     * @param replyId used to look up the answer
     * @return Answer matching the id
     */
    Reply takeReply(String replyId);

    /**
     * Returns all answers associated with the specified ballot.
     * If the ballot is <code>null</code> or has no answers,
     * an empty list is returned.
     *
     * @param ballot used to retrieve answers
     * @return List of answers from the ballot;
     * may be empty but guaranteed to not be <code>null</code>
     */
    List<Reply> pullReplies(Ballot ballot);

    /**
     * Finds the question associated with the specified question id
     * from within the list of specified answers.  If none of the
     * answers matches the requested question, this looks up the
     * question by id alone.
     *
     * @param replies    used to find the desired question
     * @param issueId used to look up the question
     * @return Question matching the id
     */
    Issue pullIssue(List<Reply> replies, String issueId);

    /**
     * Gets the answer to the given question in list of answers.
     * Should return null is there is no answer to the given question.
     *
     * @param replies  List used to locate the matching question
     * @param issue whose answer is desired
     * @return Answer to question; may be <code>null</code>
     */
    Reply takeReply(List<Reply> replies, Issue issue);

    /**
     * Gets the ballot associated with the given ballot id.
     *
     * @param permissionKey used to look up the ballot
     * @param survey        used to look up the ballot
     * @return Ballot matching the id
     */
    Ballot getBallot(PermissionKey permissionKey, Survey survey);

    /**
     * Gets the set of all ballots associated with every election.
     * The ballots that are returned are not sorted by election.
     *
     * @return Set of all Ballots
     */
    Set<Ballot> obtainBallots();

    /**
     * Returns all ballots associated with the specified election.
     * If no ballots exist for the election,
     * an empty set is returned.
     *
     * @return Set of Ballots associated with the given election
     */
    Set<Ballot> fetchBallots(Survey survey);

    /**
     * Returns all ballots associated with the specified election id.
     * If no ballots exist for the election associated with the id,
     * an empty set is returned.
     *
     * @return Set of Ballots associated with the given election id
     */
    Set<Ballot> takeBallots(String surveyId);

    /**
     * Saves the election if it doesn't exist.
     * Updates the election if it already exists.
     *
     * @param survey to be updated
     * @return boolean true if the election is added or updated
     */
    boolean addOrUpdateSurvey(Survey survey);

    /**
     * Saves the question if it doesn't exist.
     * Updates the question if it already exists.
     *
     * @param issue to be updated
     * @return boolean true if the question is added or updated
     */
    boolean addOrUpdateIssue(Issue issue);

    /**
     * Saves the choice if it doesn't exist.
     * Updates the choice if it already exists.
     *
     * @param choice to be updated
     * @return boolean true if the choice is added or updated
     */
    boolean addOrUpdateChoice(Choice choice);

    /**
     * Saves the voter if it doesn't exist.
     * Updates the voter if it already exists.
     *
     * @param voter to be updated
     * @return boolean true if the voter is added or updated
     */
    boolean addOrUpdateVoter(Voter voter);

    /**
     * Saves the answer if it doesn't exist.
     * Updates the answer if it already exists.
     *
     * @param reply to be updated
     * @return boolean true if the answer is added or updated
     */
    boolean addOrUpdateReply(Reply reply);

    /**
     * Saves the ballot if it doesn't exist.
     * Updates the ballot if it already exists.
     *
     * @param ballot to be updated
     * @return boolean true if the ballot is added or updated
     */
    boolean addOrUpdateBallot(Ballot ballot);

    /**
     * Saves or updates the results of an election combined from all servers
     *
     * @param accruedOutcomes Current results of an election from all servers
     * @return boolean true if the results were added or updated
     */
    boolean addOrUpdateOutcomes(SurveyOutcomes accruedOutcomes);

    /**
     * Deletes the answer.
     *
     * @param reply to be deleted
     * @return boolean true if successfully deleted
     */
    boolean deleteReply(Reply reply);

    /**
     * Deletes the ballot.
     *
     * @param ballot to be deleted
     * @return boolean true if successfully deleted
     */
    boolean deleteBallot(Ballot ballot);

    /**
     * Verify that the registrationKey maps to the
     * specified election and voter.
     *
     * @param survey        to verify
     * @param voter           to verify
     * @param permissionKey voter's registration key
     * @return boolean true if the voter and registration key match for this election
     */
    boolean confirmPermissionKey(Survey survey, Voter voter, PermissionKey permissionKey);

    /**
     * Get the results (so far, on this server) of an election.
     *
     * @param survey used to locate the current results
     * @return ElectionResults locally stored;
     * may be <code>null</code> if no results exist
     * @throws DirectVoteBad if there is trouble retrieving the results
     */
    SurveyOutcomes obtainLocalSurveyOutcomes(Survey survey) throws DirectVoteBad;

    /**
     * Get the results (so far, on this server) of an election.
     *
     * @param surveyId used to locate the current results
     * @return ElectionResults locally stored;
     * may be <code>null</code> if no results exist
     * @throws DirectVoteBad if there is trouble retrieving the results
     */
    SurveyOutcomes fetchLocalSurveyOutcomes(String surveyId) throws DirectVoteBad;

    /**
     * Get the results of an election that have been accrued so far, from all servers
     */
    SurveyOutcomes fetchAccruedSurveyOutcomes(Survey survey);

    /**
     * Initiate process of getting current election results from other servers
     */
    void updateOutcomes(Survey survey) throws DirectVoteBad;

    /**
     * Create a ballotId
     *
     * @param permissionKey for a ballot
     * @param surveyId      for a ballot
     * @return encrypted string of the registrationKey and electionId
     */
    String formBallotId(String permissionKey, String surveyId);

    /**
     * Create an answerId
     *
     * @param ballotId   for an answer
     * @param issueId for an answer
     * @return encrypted string of the ballotId and questionId
     */
    String formReplyId(String ballotId, String issueId);

    /**
     * Create a questionId
     *
     * @param surveyId for a Question
     * @return a unique id for a Question
     */
    String formIssueId(String surveyId);

    /**
     * Create a choiceId
     *
     * @param surveyId for a Choice
     * @param issueId for a Choice
     * @return a unique id for a Choice
     */
    String formChoiceId(String surveyId, String issueId);

    /**
     * Create an electionId
     *
     * @return a unique id for an Election
     */
    String formSurveyId();


    /**
     * When the last answer is serialized, extra answer
     * choices are added.
     * <p>
     * Note: We will only use this method to fill up space in SerializeVisitor.
     * This method should not be used anywhere else.
     *
     * @param count number of final choices to create
     * @return String array representing Answer choices
     */
    static String[] formFinalSelections(int count) {
        String[] finalSelections = new String[count];
        java.util.Arrays.fill(finalSelections, "FINALCHOICES");
        return finalSelections;
    }
}
