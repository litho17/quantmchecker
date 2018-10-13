package simplevote_1.com.cyberpointllc.stac.basicvote;

import simplevote_1.com.cyberpointllc.stac.wrapper.LZW;
import simplevote_1.com.cyberpointllc.stac.wrapper.TST;
import simplevote_1.com.cyberpointllc.stac.proto.Simplevotemsg;
import simplevote_1.com.cyberpointllc.stac.basicvote.accumulation.OutcomesMessageCreator;

import java.io.IOException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.UUID;

/**
 * Class for holding the aggregated results of a single election
 */
public class SurveyOutcomes implements VoteVisited {
    private static final String IGNORED_PREFIX = "\t";
    private static final SimpleDateFormat FORM = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");

    // Since results may be requested multiple times for the same election, this identifies the request
    private String requestId;
    private Date timestamp;
    private String surveyId;
    private int eligibleVoters;
    private int participatingVoters;

    // Maps question id to Map of answer to tally count
    private Map<String, Map<String, Integer>> tallies = new HashMap<>();

    private TST<Integer> trie = null; // trie for proto messages

    private static Date parseTimestamp(String timestamp) throws IOException {
        Date date;

        if (timestamp == null) {
            throw new IOException("Timestamp may not be null");
        }

        synchronized (FORM) {
            try {
                date = FORM.parse(timestamp);
            } catch (ParseException e) {
                throw new IOException(e); // serializers expect an IOException
            }
        }

        return date;
    }

    private static String formTimestamp(Date date) {
        if (date == null) {
            throw new IllegalArgumentException("Date may not be null");
        }

        synchronized (FORM) {
            return FORM.format(date);
        }
    }

    public SurveyOutcomes(String surveyId, int eligibleVoters) throws IOException {
        this(surveyId, eligibleVoters, 0, Collections.<String, Map<String, Integer>>emptyMap());
    }

    public SurveyOutcomes(String surveyId, int eligibleVoters, int participatingVoters, Map<String, Map<String, Integer>> outcomes) throws IOException {
        this(UUID.randomUUID().toString(), formTimestamp(new Date()), surveyId, eligibleVoters, participatingVoters, outcomes);
    }

    public SurveyOutcomes(String requestId, String timestamp, String surveyId, int eligibleVoters, int participatingVoters, Map<String, Map<String, Integer>> outcomes) throws IOException {
        if ((requestId == null) || requestId.trim().isEmpty()) {
            throw new IllegalArgumentException("Request id may not be null or empty");
        }

        if ((timestamp == null) || timestamp.trim().isEmpty()) {
            throw new IllegalArgumentException("Timestamp may not be null or empty");
        }

        if ((surveyId == null) || surveyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Election id may not be null or empty");
        }

        this.requestId = requestId.trim();
        this.timestamp = parseTimestamp(timestamp.trim());
        this.surveyId = surveyId.trim();
        this.eligibleVoters = (eligibleVoters < 0) ? 0 : eligibleVoters;
        this.participatingVoters = (participatingVoters < 0) ? 0 : participatingVoters;

        if (outcomes != null) {
            for (String issueId : outcomes.keySet()) {
                this.tallies.put(issueId, getMostPopularReplies(outcomes.get(issueId), Issue.MAXIMUM_COUNT_OF_SELECTIONS));
            }
        }
    }

    public SurveyOutcomes(Simplevotemsg.ElectionResultsMessage msg) throws IOException {
        try {
            requestId = msg.getRequestId().trim();
            timestamp = parseTimestamp(msg.getTimestamp().trim());
            surveyId = msg.getElectionId().trim();
            eligibleVoters = Integer.parseInt(msg.getEligibleVoters().trim());
            participatingVoters = Integer.parseInt(msg.getParticipatingVoters().trim());

            if (eligibleVoters < 0) {
                eligibleVoters = 0;
            }

            if (participatingVoters < 0) {
                participatingVoters = 0;
            }

            for (int issueIndex = 0; issueIndex < msg.getQuestionCount(); issueIndex++) {
                String issueId = msg.getQuestion(issueIndex);
                if (issueId.startsWith(IGNORED_PREFIX)) { // dummy entry
                    continue;
                }
                issueId = issueId.trim();

                Map<String, Integer> replyCounts = new HashMap<>();
                Simplevotemsg.AnswerTally tally = msg.getAnswerTally(issueIndex);
                // can assume number of answers was checked before message was created
                for (int replyIndex = 0; replyIndex < tally.getAnswerIdCount(); replyIndex++) {
                    String replyId = tally.getAnswerId(replyIndex);
                    if (replyId.startsWith(IGNORED_PREFIX)) { // dummy entry
                        continue;
                    }

                    replyId = replyId.trim(); // trim padding
                    int count = Integer.parseInt(tally.getVoteCount(replyIndex).trim());

                    if (count >= 0) {
                        replyCounts.put(replyId, count);
                    }
                }

                // only keep the top answers
                tallies.put(issueId, getMostPopularReplies(replyCounts, Issue.MAXIMUM_COUNT_OF_SELECTIONS));
            }

            // pull the trie out of the summary field
            byte[] summary = msg.getSummary().toByteArray();
            trie = LZW.readTrie(summary);
            OutcomesMessageCreator.defineThreshold(msg.getThreshold());
        } catch (NumberFormatException e) {
            throw new IOException("Trouble parsing message", e);
        }
    }

    public String obtainRequestId() {
        return requestId;
    }

    public Date obtainTimestamp() {
        return timestamp;
    }

    public String obtainTimestampString() {
        return formTimestamp(timestamp);
    }

    public String takeSurveyId() {
        return surveyId;
    }

    public int fetchEligibleVoters() {
        return eligibleVoters;
    }

    public int grabParticipatingVoters() {
        return participatingVoters;
    }

    public Map<String, Map<String, Integer>> obtainOutcomes() {
        return tallies;
    }

    public TST<Integer> obtainTrie() {
        return trie;
    }

    /**
     * Combine results (from different servers).
     * If the argument is <code>null</code>,
     * the request is silently ignored.
     * If the argument is for a different election than the
     * election for this result instance, then an exception is raised.
     *
     * @param otherOutcomes to be combined with these
     * @throws DirectVoteBad if the results are not from the same election
     */
    public void addOutcomes(SurveyOutcomes otherOutcomes) throws DirectVoteBad {
        if (otherOutcomes == null) {
            return;
        }

        if (!surveyId.equals(otherOutcomes.takeSurveyId())) {
            throw new DirectVoteBad("Attempted to combine results from two different elections");
        }

        eligibleVoters += otherOutcomes.fetchEligibleVoters();
        participatingVoters += otherOutcomes.grabParticipatingVoters();

        Map<String, Map<String, Integer>> otherTallies = otherOutcomes.obtainOutcomes();
        for (String issueId : otherTallies.keySet()) {
            // combine tallies
            Map<String, Integer> otherReplyCounts = otherTallies.get(issueId);
            Map<String, Integer> myReplyCounts = tallies.get(issueId);

            if (myReplyCounts == null) {
                myReplyCounts = new HashMap<>();
            }

            for (String replyId : otherReplyCounts.keySet()) {
                int myCount = 0;
                if (myReplyCounts.containsKey(replyId)) {
                    myCount = myReplyCounts.get(replyId);

                    if (myCount < 0) {
                        myCount = 0;
                    }
                }

                int otherCount = otherReplyCounts.get(replyId);
                if (otherCount > 0) {
                    myCount += otherCount;
                }

                myReplyCounts.put(replyId, myCount);
            }

            // only keep the top answers
            tallies.put(issueId, getMostPopularReplies(myReplyCounts, Issue.MAXIMUM_COUNT_OF_SELECTIONS));
        }
    }

    @Override
    public void accept(VoteVisitor visitor) throws IOException {
        visitor.visit(this);
    }

    private Map<String, Integer> getMostPopularReplies(Map<String, Integer> tallies, int count) {
        if (tallies.size() <= count) {
            return tallies;
        }

        List<Map.Entry<String, Integer>> list = new LinkedList<>(tallies.entrySet());
        Collections.sort(list, Collections.reverseOrder(new Comparator<Map.Entry<String, Integer>>() {
            public int compare(Map.Entry<String, Integer> o1, Map.Entry<String, Integer> o2) {
                return (o1.getValue()).compareTo(o2.getValue());
            }
        }));

        Map<String, Integer> outcome = new LinkedHashMap<>();
        for (int a = 0; a < count; a++) {
            Map.Entry<String, Integer> entry = list.get(a);
            outcome.put(entry.getKey(), entry.getValue());
        }

        return outcome;
    }
}
