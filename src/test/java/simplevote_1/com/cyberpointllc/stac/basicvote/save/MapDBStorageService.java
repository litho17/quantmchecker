package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.DESHelper;
import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.basicvote.StorageService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import org.mapdb.DB;
import org.mapdb.DBMaker;
import org.mapdb.Serializer;

import java.io.File;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public class MapDBStorageService implements StorageService {
    private static final Map<String, PermissionKey> EMPTY_PERMISSION_KEY_MAP = Collections.emptyMap();

    private static final String SURVEY_MAP = "elections";
    private static final String ISSUE_MAP = "questions";
    private static final String CHOICE_MAP = "choices";
    private static final String VOTER_MAP = "voters";
    private static final String REPLY_MAP = "answers";
    private static final String BALLOT_MAP = "ballots";
    private static final String OUTCOMES_MAP = "results"; // these include results from other servers
    private static final String SURVEY_VOTER_KEY_MAP = "electionToVoterToKey";

    private final DB database;
    private final String passwordKey;
    private int uniqueIdCounter;

    /**
     * Maps Election id to Election
     */
    private final Map<String, Survey> surveys;

    /**
     * Maps Question id to Question
     */
    private final Map<String, Issue> issues;

    /**
     * Maps Choice id to Choice
     */
    private final Map<String, Choice> selections;

    /**
     * Maps Voter id to Voter
     */
    private final Map<String, Voter> voters;

    /**
     * Maps Answer id to Answer
     */
    private final Map<String, Reply> replies;

    /**
     * Maps Ballot id to Ballot
     */
    private final Map<String, Ballot> ballots;

    /**
     * Maps Election Result id to Election Result (from all servers)
     */
    private final Map<String, SurveyOutcomes> outcomes;

    /**
     * Each Election has a registration key for each voter allowed to
     * vote in that election.  The keys are public after the election,
     * but their associated voters are secret.
     */
    private final Map<String, Map<String, PermissionKey>> surveysToVotersToKeys;

    public MapDBStorageService(File file, String passwordKey) {
        if (file == null) {
            throw new IllegalArgumentException("File cannot be null");
        }

        database = DBMaker.fileDB(file).fileMmapEnableIfSupported().transactionDisable().asyncWriteEnable().make();
        this.passwordKey = passwordKey;
        this.uniqueIdCounter = 1;

        surveys = database.hashMap(SURVEY_MAP, Serializer.STRING, new SurveyEncoder());
        issues = database.hashMap(ISSUE_MAP, Serializer.STRING, new IssueEncoder());
        selections = database.hashMap(CHOICE_MAP, Serializer.STRING, new ChoiceEncoder());
        voters = database.hashMap(VOTER_MAP, Serializer.STRING, new VoterEncoder());
        replies = database.hashMap(REPLY_MAP, Serializer.STRING, new ReplyEncoder());
        ballots = database.hashMap(BALLOT_MAP, Serializer.STRING, new BallotEncoder());
        outcomes = database.hashMap(OUTCOMES_MAP, Serializer.STRING, new OutcomesEncoder());
        surveysToVotersToKeys = database.hashMap(SURVEY_VOTER_KEY_MAP, Serializer.STRING, new PermissionKeyMapEncoder());
    }

    @Override
    public void commit() {
        database.commit();
    }

    @Override
    public void close() {
        database.commit();
        database.close();
    }

    @Override
    public Set<Survey> obtainSurveys() {
        return new LinkedHashSet<>(surveys.values());
    }

    @Override
    public Set<Issue> takeIssues() {
        return new LinkedHashSet<>(issues.values());
    }

    @Override
    public Set<String> takeChoiceIds() {
        return selections.keySet();
    }

    @Override
    public Set<Choice> fetchSelections() {
        return new LinkedHashSet<>(selections.values());
    }

    @Override
    public Set<Voter> obtainVoters() {
        return new LinkedHashSet<>(voters.values());
    }

    @Override
    public Set<Reply> takeReplies() {
        return new LinkedHashSet<>(replies.values());
    }

    @Override
    public Set<Ballot> fetchBallots() {
        return new LinkedHashSet<>(ballots.values());
    }

    @Override
    public Survey fetchSurvey(String surveyId) {
        if (surveyId == null || surveyId.isEmpty()) {
            throw new IllegalArgumentException("Election ID can't be null or empty.");
        }
        return surveys.get(surveyId.trim());

    }

    @Override
    public Issue takeIssue(String issueId) {
        if (issueId == null || issueId.isEmpty()) {
            throw new IllegalArgumentException("Question ID can't be null or empty.");
        }
        return issues.get(issueId.trim());

    }

    @Override
    public Choice takeChoice(String choiceId) {
        if (choiceId == null || choiceId.isEmpty()) {
            throw new IllegalArgumentException("Choice ID can't be null or empty.");
        }
        return selections.get(choiceId.trim());

    }

    @Override
    public Voter grabVoter(String voterId) {
        if (voterId == null || voterId.isEmpty()) {
            throw new IllegalArgumentException("Voter ID can't be null or empty.");
        }
        return voters.get(voterId.trim());

    }

    @Override
    public Reply getReply(String replyId) {
        if (replyId == null || replyId.isEmpty()) {
            throw new IllegalArgumentException("Answer ID can't be null or empty.");
        }

        return replies.get(replyId.trim());
    }

    @Override
    public Ballot pullBallot(PermissionKey permissionKey, Survey survey) {
        String ballotId = formBallotId(permissionKey.grabKey(), survey.obtainSurveyId());

        return ballots.get(ballotId.trim());
    }

    @Override
    public Set<Ballot> takeBallots(String surveyId) {
        // Get the current ballots, even if they are not finalized.
        // This leaks information, but not in a STAC-specific way.
        Set<Ballot> outcomes = new LinkedHashSet<>();

        if ((surveyId != null) && !surveyId.trim().isEmpty()) {
            surveyId = surveyId.trim();

            for (Ballot ballot : ballots.values()) {
                if (ballot.pullSurveyId().equals(surveyId)) {
                    outcomes.add(ballot);
                }
            }
        }

        return outcomes;
    }

    @Override
    public SurveyOutcomes fetchAccruedSurveyOutcomes(String surveyId) {
        if (surveyId == null || surveyId.isEmpty()) {
            throw new IllegalArgumentException("Election ID can't be null or empty.");
        }

        return outcomes.get(surveyId.trim());
    }

    @Override
    public Map<String, PermissionKey> pullPermissionKeysForSurvey(String surveyId) {
        Map<String, PermissionKey> outcomes = null;

        if ((surveyId != null) && !surveyId.trim().isEmpty()) {
            outcomes = surveysToVotersToKeys.get(surveyId.trim());
        }

        return (outcomes == null) ? EMPTY_PERMISSION_KEY_MAP : outcomes;
    }

    @Override
    public boolean addOrUpdateSurvey(Survey survey) {
        if (survey == null) {
            throw new IllegalArgumentException("Election can't be null.");
        }

        String surveyId = survey.obtainSurveyId();

        // commit when updating an election
        boolean commit = surveys.containsKey(surveyId);
        surveys.put(surveyId, survey);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateIssue(Issue issue) {
        if (issue == null) {
            throw new IllegalArgumentException("Question can't be null.");
        }

        String issueId = issue.grabIssueId();

        // commit when updating a question
        boolean commit = issues.containsKey(issueId);
        issues.put(issueId, issue);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateChoice(Choice choice) {
        if (choice == null) {
            throw new IllegalArgumentException("Choice can't be null.");
        }

        String choiceId = choice.pullChoiceId();

        // commit when updating a choice
        boolean commit = selections.containsKey(choiceId);
        selections.put(choiceId, choice);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateVoter(Voter voter) {
        if (voter == null) {
            throw new IllegalArgumentException("Voter can't be null.");
        }

        String voterId = voter.obtainUnity();

        // commit when updating a voter
        boolean commit = voters.containsKey(voterId);
        voters.put(voterId, voter);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateReply(Reply reply) {
        if (reply == null) {
            throw new IllegalArgumentException("Answer can't be null.");
        }

        String replyId = reply.pullReplyId();

        // commit when updating an answer
        boolean commit = replies.containsKey(replyId);
        replies.put(replyId, reply);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateBallot(Ballot ballot) {
        if (ballot == null) {
            throw new IllegalArgumentException("Ballot can't be null.");
        }

        String ballotId = ballot.pullBallotId();

        // commit when updating a ballot
        boolean commit = ballots.containsKey(ballotId);
        ballots.put(ballot.pullBallotId(), ballot);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean addOrUpdateOutcomes(SurveyOutcomes accruedOutcomes) {
        if (accruedOutcomes == null) {
            throw new IllegalArgumentException("ElectionResults can't be null.");
        }

        String surveyId = accruedOutcomes.takeSurveyId();

        // commit when updating
        boolean commit = outcomes.containsKey(surveyId);
        outcomes.put(surveyId, accruedOutcomes);
        if (commit) {
            database.commit();
        }
        return true;
    }

    @Override
    public boolean deleteSurvey(String surveyId) {
        if (surveyId == null || surveyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Election ID can't be null or empty.");
        }

        return surveys.remove(surveyId.trim()) != null;
    }

    @Override
    public boolean deleteIssue(String issueId) {
        if (issueId == null || issueId.trim().isEmpty()) {
            throw new IllegalArgumentException(("Question ID can't be null or empty."));
        }

        return issues.remove(issueId.trim()) != null;

    }

    @Override
    public boolean deleteChoice(String choiceId) {
        if (choiceId == null || choiceId.trim().isEmpty()) {
            throw new IllegalArgumentException("Choice ID can't be null or empty.");
        }

        return selections.remove(choiceId.trim()) != null;
    }

    @Override
    public boolean deleteVoter(String voterId) {
        if (voterId == null || voterId.trim().isEmpty()) {
            throw new IllegalArgumentException("Voter ID can't be null or empty.");
        }
        return voters.remove(voterId.trim()) != null;
    }

    @Override
    public boolean deleteReply(String replyId) {
        if (replyId == null || replyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Answer ID can't be null or empty.");
        }

        return replies.remove(replyId.trim()) != null;
    }

    @Override
    public boolean deleteBallot(String ballotId) {
        if (ballotId == null || ballotId.trim().isEmpty()) {
            throw new IllegalArgumentException("Ballot ID can't be null or empty.");
        }

        return ballots.remove(ballotId.trim()) != null;
    }

    @Override
    public void addIssue(Issue issue) {
        if (issue == null) {
            throw new IllegalArgumentException("Question can't be null.");
        }

        String issueId = issue.grabIssueId();

        if (issues.containsKey(issueId)) {
            throw new IllegalArgumentException("Question ID " + issueId + " Already exists in the database");
        }
        issues.put(issueId, issue);
    }

    @Override
    public void addChoice(Choice choice) {
        if (choice == null) {
            throw new IllegalArgumentException("Choice can't be null.");
        }

        String choiceId = choice.pullChoiceId();

        if (selections.containsKey(choiceId)) {
            throw new IllegalArgumentException("Choice ID " + choiceId + " Already exists in the database");
        }
        selections.put(choiceId, choice);
    }

    @Override
    public void addVoter(Voter voter) {
        if (voter == null) {
            throw new IllegalArgumentException("Voter can't be null.");
        }

        String voterId = voter.obtainUnity();

        if (voters.containsKey(voterId)) {
            throw new IllegalArgumentException("Voter ID " + voterId + " Already exists in the database");
        }
        voters.put(voterId, voter);
    }

    @Override
    public void addReply(Reply reply) {
        if (reply == null) {
            throw new IllegalArgumentException("Answer can't be null.");
        }

        String replyId = reply.pullReplyId();

        if (replies.containsKey(replyId)) {
            throw new IllegalArgumentException("Answer ID " + replyId + " Already exists in the database");
        }
        replies.put(replyId, reply);
    }

    @Override
    public void addBallot(Ballot ballot) {
        if (ballot == null) {
            throw new IllegalArgumentException("Ballot can't be null.");
        }

        String ballotId = ballot.pullBallotId();

        if (ballots.containsKey(ballotId)) {
            throw new IllegalArgumentException("Ballot ID " + ballotId + " Already exists in the database");
        }
        ballots.put(ballotId, ballot);
    }

    @Override
    public void addPermissionKey(PermissionKey permissionKey, String surveyId, String voterId) {
        if (permissionKey == null) {
            throw new IllegalArgumentException("Registration key may not be null");
        }

        if ((surveyId == null) || surveyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Election Id may not be null or empty");
        }

        if ((voterId == null) || voterId.trim().isEmpty()) {
            throw new IllegalArgumentException("Voter Id may not be null or empty");
        }

        Map<String, PermissionKey> votersToKeys = surveysToVotersToKeys.computeIfAbsent(surveyId.trim(), k -> new HashMap<>());
        votersToKeys.put(voterId, permissionKey);
    }

    @Override
    public void cleanDatabase() {
        Date today = new Date();
        Survey survey = null;
        Set<Map.Entry<String, PermissionKey>> voterToRegKeyAssign = null;

        Ballot[] allBallots = ballots.values().toArray(new Ballot[ballots.size()]);
        Arrays.sort(allBallots, Comparator.comparing(Ballot::pullSurveyId));

        for (int j = 0; j < allBallots.length; j++) {
            Ballot ballot = allBallots[j];
            if ((survey == null) || !survey.obtainSurveyId().equals(ballot.pullSurveyId())) {
                survey = fetchSurvey(ballot.pullSurveyId());
                voterToRegKeyAssign = pullPermissionKeysForSurvey(survey.obtainSurveyId()).entrySet();
            }

            if (!survey.isSurveyActive(today)) {
                // (If ballot is from a past election and not finalized) OR (If ballot is for future election)
                if ((survey.isAfterSurveyEnd(today) && !ballot.isFinalized()) || survey.isBeforeSurveyStart(today)) {
                    cleanBallot(ballot, voterToRegKeyAssign);
                }
            }
        }
    }

    private void cleanBallot(Ballot ballot, Set<Map.Entry<String, PermissionKey>> voterToRegKeyDefine) {
        System.out.println("Deleting invalid ballot: " + ballot.pullBallotId());
        // Remove the voters election status for the corresponding ballot
        if (voterToRegKeyDefine != null) {
            for (Map.Entry<String, PermissionKey> voterToRegKey : voterToRegKeyDefine) {
                if (voterToRegKey.getValue().equals(ballot.takePermissionKey())) {
                    Voter voter = grabVoter(voterToRegKey.getKey());
                    if (voter != null) {
                        voter.releaseSurveyStatus(ballot.pullSurveyId());
                        addOrUpdateVoter(voter);
                        break;
                    }
                }
            }
        }

        deleteBallot(ballot.pullBallotId());
    }

    @Override
    public String summary() {
        return "The Database contains:\n" +
                surveys.size() + " Elections\n" +
                issues.size() + " Questions\n" +
                selections.size() + " Choices\n" +
                voters.size() + " Voters\n" +
                ballots.size() + " Ballots\n" +
                replies.size() + " Answers\n" +
                surveysToVotersToKeys.values().stream().mapToInt(Map::size).sum() + " Registration Keys";
    }

    @Override
    public String formBallotId(String permissionKey, String surveyId) {
        return DESHelper.grabEncryptedString(permissionKey.trim() + "@" + surveyId.trim(), passwordKey);
    }

    @Override
    public String formReplyId(String ballotId, String issueId) {
        return ballotId.trim() + "@" + issueId.trim();
    }

    @Override
    public String formIssueId(String surveyId) {
        return Integer.toString(++uniqueIdCounter);
    }

    @Override
    public String formChoiceId(String surveyId, String issueId) {
        return Integer.toString(++uniqueIdCounter);
    }

    @Override
    public String formSurveyId() {
        return Integer.toString(++uniqueIdCounter);
    }
}
