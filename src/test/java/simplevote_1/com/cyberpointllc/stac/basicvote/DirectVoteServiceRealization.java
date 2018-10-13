package simplevote_1.com.cyberpointllc.stac.basicvote;

import simplevote_1.com.cyberpointllc.stac.basicvote.accumulation.CompilationService;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Used by SimpleVote to interact with the storage service.
 */
public class DirectVoteServiceRealization implements DirectVoteService {
    private static final Logger logger = LoggerFactory.getLogger(DirectVoteServiceRealization.class);

    private static final int UPDATE_INTERVAL = 10;
    private static final long WAIT_TIME = 5;

    private final StorageService storageService;
    private final CompilationService compilationService;
    private final Map<String, Integer> surveyUpdates;
    private final Object lock = new Object();

    private boolean votingActivated;

    public DirectVoteServiceRealization(StorageService storageService, CompilationService compilationService) {
        this.storageService = storageService;
        this.compilationService = compilationService;
        compilationService.defineDirectVoteService(this);
        surveyUpdates = new LinkedHashMap<>();
        votingActivated = true;
    }

    @Override
    public boolean isVotingActivated() {
        synchronized(lock) {
            try {
                lock.wait(WAIT_TIME);
            } catch (InterruptedException e) {
                logger.warn("Unexpected interruption", e);
            }
        }

        return votingActivated;
    }

    @Override
    public void fixVotingActivated(boolean activated) {
        synchronized(lock) {
            votingActivated = activated;
            lock.notifyAll();
        }
    }

    @Override
    public Voter pullVoter(String voterId) {
        return storageService.grabVoter(voterId);
    }

    @Override
    public Set<Voter> fetchVoters() {
        return storageService.obtainVoters();
    }

    @Override
    public Set<Survey> pullSurveys() {
        return storageService.obtainSurveys();
    }

    @Override
    public Survey fetchSurvey(String surveyId) {
        return storageService.fetchSurvey(surveyId);
    }

    @Override
    public Set<Issue> obtainIssues(Survey survey) {
        Set<String> issueIds = survey.getIssueIds();

        Set<Issue> issues = new LinkedHashSet<>();
        for (String issueId : issueIds) {
            Issue issue = storageService.takeIssue(issueId);
            issues.add(issue);
        }

        return issues;
    }

    @Override
    public Issue takeIssue(String issueId) {
        Issue issue = storageService.takeIssue(issueId);

        if (issue == null) {
            issue =  storageService.getReply(issueId);
        }

        return issue;
    }

    @Override
    public Set<Choice> getSelections(Issue issue) {
        Set<String> choiceIds = issue.obtainChoiceIds();

        Set<Choice> selections = new LinkedHashSet<>();
        for (String choiceId : choiceIds) {
            Choice choice = pullChoice(choiceId);
            selections.add(choice);
        }
        return selections;
    }

    @Override
    public Choice pullChoice(String choiceId) {
        return storageService.takeChoice(choiceId);
    }

    @Override
    public Set<Voter> pullEligibleVoters(String surveyId) {
        Set<Voter> eligibleVoters = new LinkedHashSet<>();

        for (Voter voter : fetchVoters()) {
            if (voter.isEligible(surveyId)) {
                eligibleVoters.add(voter);
            }
        }

        return eligibleVoters;
    }

    @Override
    public int countEligibleVoters(String surveyId) {
        Map<String, PermissionKey> voterToKeys = storageService.pullPermissionKeysForSurvey(surveyId);
        return voterToKeys.size();
    }

    @Override
    public int countParticipatingVoters(String surveyId) {
         int finalizedCount = 0;

         for (Ballot ballot : takeBallots(surveyId)) {
             if (ballot.isFinalized()) {
                 finalizedCount++;
             }
         }

         return finalizedCount;
    }

    @Override
    public Reply takeReply(String replyId) {
        return storageService.getReply(replyId);
    }

    @Override
    public List<Reply> pullReplies(Ballot ballot) {
        List<Reply> replies = new ArrayList<>();

        if (ballot != null) {
            for (String replyId : ballot.obtainReplies()) {
                Reply reply = takeReply(replyId);

                if (reply != null) {
                    replies.add(reply);
                }
            }
        }

        return replies;
    }

    @Override
    public Issue pullIssue(List<Reply> replies, String issueId) {
        if (replies != null) {
            for (int b = 0; b < replies.size(); b++) {
                Reply reply = replies.get(b);
                if (reply.pullReplyId().equals(issueId)) {
                    return reply;
                } else if ((reply.pullIssue() != null) && reply.pullIssue().grabIssueId().equals(issueId)) {
                    return reply.pullIssue();
                }
            }
        }

        return takeIssue(issueId);
    }

    @Override
    public Reply takeReply(List<Reply> replies, Issue issue) {
        String issueId = issue.grabIssueId();

        while (issue instanceof Reply) {
            issue = ((Reply) issue).pullIssue();
        }
        if (replies != null) {
            for (int b = 0; b < replies.size(); b++) {
                Reply reply = replies.get(b);
                if ((reply != null) && reply.grabIssueId().equals(issueId)) {
                    reply.defineIssue(issue);

                    return reply;
                }
            }
        }

        return null;
    }

    @Override
    public Ballot getBallot(PermissionKey permissionKey, Survey survey) {
        return storageService.pullBallot(permissionKey, survey);
    }

    @Override
    public Set<Ballot> obtainBallots() {
        return storageService.fetchBallots();
    }

    @Override
    public Set<Ballot> fetchBallots(Survey survey) {
        return takeBallots(survey.obtainSurveyId());
    }

    @Override
    public Set<Ballot> takeBallots(String surveyId) {
        return storageService.takeBallots(surveyId);
    }

    @Override
    public boolean addOrUpdateSurvey(Survey survey) {
        return storageService.addOrUpdateSurvey(survey);
    }

    @Override
    public boolean addOrUpdateIssue(Issue issue) {
        return storageService.addOrUpdateIssue(issue);
    }

    @Override
    public boolean addOrUpdateChoice(Choice choice) {
        return storageService.addOrUpdateChoice(choice);
    }

    @Override
    public boolean addOrUpdateVoter(Voter voter) {
        return storageService.addOrUpdateVoter(voter);
    }

    @Override
    public boolean addOrUpdateReply(Reply reply) {
        return storageService.addOrUpdateReply(reply);
    }

    @Override
    public boolean addOrUpdateBallot(Ballot ballot) {
        updateSurvey(ballot.pullSurveyId());
        return storageService.addOrUpdateBallot(ballot);
    }

    @Override
    public boolean addOrUpdateOutcomes(SurveyOutcomes accruedOutcomes) {
        return storageService.addOrUpdateOutcomes(accruedOutcomes);
    }

    @Override
    public boolean deleteReply(Reply reply) {
        return storageService.deleteReply(reply.pullReplyId());
    }

    @Override
    public boolean deleteBallot(Ballot ballot) {
        return storageService.deleteBallot(ballot.pullBallotId());
    }

    @Override
    public boolean confirmPermissionKey(Survey survey, Voter voter, PermissionKey permissionKey) {
        if ((survey == null) || (voter == null) || (permissionKey == null)) {
            return false;
        }

        Map<String, PermissionKey> voterToKeys = storageService.pullPermissionKeysForSurvey(survey.obtainSurveyId());

        return voterToKeys.containsValue(permissionKey);
        }

    @Override
    public SurveyOutcomes obtainLocalSurveyOutcomes(Survey survey) throws DirectVoteBad {
        if (survey == null) {
            return null;
        }

        String surveyId = survey.obtainSurveyId();

        // Future Elections have no results
        if (survey.isBeforeSurveyStart(new Date())) {
            try {
                return new SurveyOutcomes(surveyId, countEligibleVoters(surveyId));
            } catch (IOException e) {
                throw new DirectVoteBad(e);
            }
        }

        Set<Ballot> ballots = fetchBallots(survey);

        // This stores the results for an entire election.
        // The key is the question id; the value is a map
        // that maps an answer id to the number of votes cast.
        Map<String, Map<String, Integer>> surveyOutcomes = new LinkedHashMap<>();

        for (String issueId : survey.getIssueIds()) {
            Issue issue = takeIssue(issueId);

            int didNotVoteCount = 0;

            Map<String, Integer> issueOutcomes;
            if (issue.isMultipleChoice()) {
                issueOutcomes = new LinkedHashMap<>();
                // add all possible answers with 0 count
                for (String choice : issue.obtainChoiceIds()) {
                   issueOutcomes.put(pullChoice(choice).getChoiceEssence(), 0);
                }
            } else {
                // Case-insensitive map so text answers match (dog == Dog)
                issueOutcomes = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
            }

            // Go through each ballot for this question
            for (Ballot ballot : ballots) {
                // Only finalized ballots are included
                if (!ballot.isFinalized()) {
                    continue;
                }

                List<Reply> replies = pullReplies(ballot);
                // Get the answer for this question on this ballot
                Reply reply = takeReply(replies, issue);

                if ((reply == null) || !reply.isAnswered()) {
                    // This ballot didn't answer this question
                    didNotVoteCount++;
                } else if (issue.isMultipleChoice()) {
                    // Increment all selected choices
                    for (String choiceId : issue.obtainChoiceIds()) {
                        if (reply.obtainChoiceIds().contains(choiceId)) {
                            String choice = pullChoice(choiceId).getChoiceEssence();
                            incrementCount(choice, issueOutcomes);
                        }
                    }
                } else {
                    incrementCount(reply.takeTextReply().trim(), issueOutcomes);
                }
            }

            if (didNotVoteCount > 0) {
                issueOutcomes.put(DID_NOT_VOTE_ID, didNotVoteCount);
            }

            // Add the question results to the overall results
            surveyOutcomes.put(issueId, issueOutcomes);
        }

        try {
            return new SurveyOutcomes(surveyId, countEligibleVoters(surveyId), countParticipatingVoters(surveyId), surveyOutcomes);
        } catch (IOException e) {
            throw new DirectVoteBad(e);
        }
    }

    @Override
    public SurveyOutcomes fetchLocalSurveyOutcomes(String surveyId) throws DirectVoteBad {
        return obtainLocalSurveyOutcomes(fetchSurvey(surveyId));
    }

    @Override
    public String formBallotId(String permissionKey, String surveyId) {
       return storageService.formBallotId(permissionKey, surveyId);
    }

    @Override
    public String formReplyId(String ballotId, String issueId) {
        return storageService.formReplyId(ballotId, issueId);
    }

    @Override
    public String formIssueId(String surveyId) {
        return storageService.formIssueId(surveyId);
    }
    @Override

    public String formChoiceId(String surveyId, String issueId) {
        return storageService.formChoiceId(surveyId, issueId);
    }

    @Override
    public String formSurveyId() {
        return storageService.formSurveyId();
    }

    /**
     * Increments the map entry corresponding to the selected key.
     * If there is no entry that maps to the specified key yet,
     * it is assigned a value of 1.
     *
     * @param key      to increment
     * @param countMap containing the map of key to count
     */
    private static void incrementCount(String key, Map<String, Integer> countMap) {
        int count = 1 + countMap.getOrDefault(key, 0);
        countMap.put(key, count);
    }

    @Override
    public SurveyOutcomes fetchAccruedSurveyOutcomes(Survey survey) {
        return (survey == null) ? null : storageService.fetchAccruedSurveyOutcomes(survey.obtainSurveyId());
    }

    @Override
    public void updateOutcomes(Survey survey) throws DirectVoteBad {
        if (survey == null) {
            return;
        }

        SurveyOutcomes localOutcomes = obtainLocalSurveyOutcomes(survey);

        if (localOutcomes != null) {
            updateOutcomesGuide(survey, localOutcomes);
        }
    }

    private void updateOutcomesGuide(Survey survey, SurveyOutcomes localOutcomes) throws DirectVoteBad {
        if (survey.isBeforeSurveyStart(new Date())) {
            // Future Election has not started yet; don't aggregate
            addOrUpdateOutcomes(localOutcomes);
        } else {
            compilationService.gatherOutcomes(survey.obtainSurveyId(), localOutcomes);
        }
    }

    private void updateSurvey(String surveyId) {
        int essence = (1 + surveyUpdates.getOrDefault(surveyId, 0)) % UPDATE_INTERVAL;
        surveyUpdates.put(surveyId, essence);

        if (essence == 0) {
            // Process all past and current elections
            new DirectVoteServiceRealizationTarget().invoke();
        }
    }

    private class DirectVoteServiceRealizationTarget {
        public void invoke() {
            Date now = new Date();
            pullSurveys().stream()
                          .filter(survey -> !survey.isBeforeSurveyStart(now))
                          .sorted(Comparator.comparing(Survey::obtainSurveyId))
                          .forEach((Survey survey) -> {
                try {
                    if (isVotingActivated()) {
                        invokeEngine(survey);
                    }
                } catch (DirectVoteBad e) {
                    logger.warn("Trouble updating election " + survey.obtainSurveyId(), e);
                }
            });
        }

        private void invokeEngine(Survey survey) throws DirectVoteBad {
            updateOutcomes(survey);

            try {
                Thread.sleep(300);
            } catch (InterruptedException e) {
                logger.warn("Pause between updates was interrupted", e);
            }
        }
    }
}
