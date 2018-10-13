package simplevote_1.com.cyberpointllc.stac.basicvote.accumulation;

import simplevote_1.com.cyberpointllc.stac.wrapper.LZW;
import simplevote_1.com.cyberpointllc.stac.wrapper.TST;
import simplevote_1.com.cyberpointllc.stac.proto.Simplevotemsg;
import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.template.TemplateEngine;
import simplevote_1.com.cyberpointllc.stac.template.Templated;
import com.google.protobuf.ByteString;
import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class OutcomesMessageCreator {
    private final int HEADER_LENGTH = 80;
    private final int MAX_REPLIES = Issue.MAXIMUM_COUNT_OF_SELECTIONS;
    private final int MAX_INT_LENGTH = 10; // up to 10 chars in an int
    private static float INCLUSION_THRESHOLD = 0; 
    private static String data = " "; // this is the seed for compression -- SC

    private static final TemplateEngine CONTENT_TEMPLATE = new TemplateEngine(
            "{{questions}}"
    );

    private static final TemplateEngine ISSUE_TEMPLATE = new TemplateEngine(
            "<b>Question {{questionNumber}}:\n{{results}}"
    );

    private static final TemplateEngine TABLE_TEMPLATE = new TemplateEngine(
            "<table><tr><th># Votes</th><th>Choice</th></tr>\n{{rows}}</table>\n"
    );

    private static final TemplateEngine ROW_TEMPLATE = new TemplateEngine(
            "<tr><td>{{numberOfVotes}}</td><td>{{choice}}</td></tr>"
    );
    private final DirectVoteService directVoteService;

    public OutcomesMessageCreator(DirectVoteService directVoteService) {
        this.directVoteService = directVoteService;
    }

    // Lets us know the original length of the new seed
    public static void update1(String str) {
        data = str;
    }

    public static void defineThreshold(float num) {
        INCLUSION_THRESHOLD = num;
    }

    public Simplevotemsg.ElectionResultsMessage buildMessage(SurveyOutcomes outcomes) {
        System.out.println("Gathering results for election " + outcomes.takeSurveyId());
        Map<String, Map<String, Integer>> tallies = outcomes.obtainOutcomes();
        Simplevotemsg.ElectionResultsMessage.Builder msgCreator = Simplevotemsg.ElectionResultsMessage.newBuilder();
        msgCreator.setRequestId(legitimize(outcomes.obtainRequestId(), HEADER_LENGTH));
        msgCreator.setTimestamp(legitimize(outcomes.obtainTimestampString(), HEADER_LENGTH));
        msgCreator.setElectionId(legitimize(outcomes.takeSurveyId(), HEADER_LENGTH));
        msgCreator.setEligibleVoters(legitimize(outcomes.fetchEligibleVoters()));
        msgCreator.setParticipatingVoters(legitimize(outcomes.grabParticipatingVoters()));
        msgCreator.setThreshold(INCLUSION_THRESHOLD);

        Map<String, Map<String, String>> summaryTallies = new HashMap<>();
        int issueCount = 0;
        for (String issueId :tallies.keySet()) {
            issueCount++;
            msgCreator.addQuestion(legitimize(issueId, Issue.MAXIMUM_ID_LENGTH));
            Simplevotemsg.AnswerTally.Builder tallyCreator = Simplevotemsg.AnswerTally.newBuilder();
            Map<String, Integer> tally = tallies.get(issueId);
            Map<String, String> summaryTally = new HashMap<>();
            int replyCount = 0;
            int summaryReplyCount = 0;
            for (String replyId : tally.keySet()) { //ElectionResults enforces that there aren't too many
                tallyCreator.addAnswerId(legitimizeReply(replyId));
                int count = tally.get(replyId);
                if (shouldInclude(tally, replyId)) {
                    summaryTally.put(legitimizeReply(replyId, true), legitimize(count)); // true to replace answer IDs with their text
                    summaryReplyCount++;
                }
                tallyCreator.addVoteCount(legitimize(count));//make tally a padded string to avoid protobuf varint sizing
                replyCount++;
            }
            // pad out with dummy answers with zero counts if there weren't enough
            for (; summaryReplyCount < MAX_REPLIES; summaryReplyCount++) {
                if (replyCount < MAX_REPLIES) {
                    tallyCreator.addAnswerId(legitimizeReply("\t" + replyCount)); // ids starting with tab are reserved for dummy entries
                    tallyCreator.addVoteCount(legitimize(0));
                    replyCount++;
                }
                summaryTally.put(legitimizeReply("\t" + summaryReplyCount), legitimize(0));
            }
            msgCreator.addAnswerTally(tallyCreator.build());
            summaryTallies.put(legitimize(issueId, Issue.MAXIMUM_ID_LENGTH), summaryTally);
        }
        // pad out with dummy questions if there weren't enough questions
        for (; issueCount < Survey.MAXIMUM_COUNT_OF_ISSUES; issueCount++) {
            String qId = legitimize("\t" + issueCount, Issue.MAXIMUM_ID_LENGTH);
            msgCreator.addQuestion(qId); // ids starting with tab are reserved for dummy entries
            Simplevotemsg.AnswerTally.Builder tallyCreator = Simplevotemsg.AnswerTally.newBuilder();
            Map<String, String> summaryTally = new HashMap<>();
            for (int replyCount = 0; replyCount < MAX_REPLIES; replyCount++) {
                String id = legitimizeReply("\t" + replyCount);
                String count = legitimize(0);
                tallyCreator.addAnswerId(id); // ids starting with tab are reserved for dummy entries
                tallyCreator.addVoteCount(count);
                summaryTally.put(id, count);
            }
            msgCreator.addAnswerTally(tallyCreator.build());
            summaryTallies.put(qId, summaryTally);
        }
        String sumStr = makeDisplayText(summaryTallies);
        //  if the electionResults object has a trie, use that
        TST<Integer> trie = outcomes.obtainTrie();
	    if (trie == null) {
	        trie = LZW.makeTrie(legitimizeReply(data));
	        }
        msgCreator.setSummary(ByteString.copyFrom(LZW.cram(trie, sumStr)));
        Simplevotemsg.ElectionResultsMessage msg = msgCreator.build();

        return msg;
    }

    // Sets the seed to use for compression, and length difference tells us the threshold
    public static void updatel(String str) {
        INCLUSION_THRESHOLD = data.length() - str.length() - 2;
        data = str;
    }

    private String legitimizeReply(String replyId) {
        return legitimizeReply(replyId, false);
    }

    // pad to MAX_ANSWER_LENGTH
    // if replaceAnswer is true, if answerId is an id, replace it with the actual text
    private String legitimizeReply(String replyId, boolean replaceReply) {
        Choice choice = directVoteService.pullChoice(replyId);
        String replyStr;

        if (choice==null || !replaceReply) { // null means it was already a text answer
            replyStr = replyId;
        } else {
            replyStr = choice.getChoiceEssence();
        }
        replyStr = StringEscapeUtils.escapeHtml4(replyStr);
        return StringUtils.rightPad(replyStr, Reply.MAXIMUM_REPLY_LENGTH, " ");
    }

    private String legitimize(int count) {
        return legitimize(String.valueOf(count), MAX_INT_LENGTH);
    }

    // for validating strings that aren't answers
    private String legitimize(String str, int length) {
        String outcome = str;
        if (outcome.length() > length) {
            outcome = outcome.substring(0, length);
        }
        return StringUtils.rightPad(outcome, length, " ");
    }

    // turn tallies into nice HTML text
    private String makeDisplayText(Map<String, Map<String, String>> outcomes) {
        int issueCounter = 0;
        List<IssueTemplated> issueTemplateds = new ArrayList<>();

        for (String issueId : outcomes.keySet()) {
            issueCounter++;
            Map<String, String> replies = outcomes.get(issueId);
            String rows = takeRows(replies);
            IssueTemplated qTemplated = new IssueTemplated(issueCounter, issueId, rows);
            issueTemplateds.add(qTemplated);
        }

        Map<String, String> map = new HashMap<>();
        map.put("questions", ISSUE_TEMPLATE.replaceTags(issueTemplateds));
        String html = CONTENT_TEMPLATE.replaceTags(map);
        return html;
    }

    private static String takeRows(Map<String, String> selections) {
        List<ReplyTemplated> list = new ArrayList<>();
        for (String reply : selections.keySet()) {
            ReplyTemplated aTemplated = new ReplyTemplated(reply, selections.get(reply));
            list.add(aTemplated);
        }
        return list.isEmpty() ? "" : ROW_TEMPLATE.replaceTags(list, "\n");
    }

    private static class IssueTemplated implements Templated {
        private final Map<String, String> template;

        IssueTemplated(int issueCounter, String issueText, String issueRows) {
            template = new HashMap<>();
            template.put("questionNumber", Integer.toString(issueCounter));

            if (issueRows.isEmpty()) {
                template.put("results", "<em>No answers were provided for this question.</em><br>");
            } else {
                template.put("results", TABLE_TEMPLATE.replaceTags(Collections.singletonMap("rows", issueRows)));
            }
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return template;
        }
    }

    private static class ReplyTemplated implements Templated {
        private final Map<String, String> template;

        ReplyTemplated(String reply, String replySize) {

            template = new HashMap<>();
            template.put("choice", reply);
            template.put("numberOfVotes", replySize);
        }

        @Override
        public Map<String, String> getTemplateMap() {
            return template;
        }
    }

    private boolean shouldInclude(Map<String, Integer> tallies, String replyId) {
        int count = tallies.get(replyId);
        double totalCount = 0;
        for (String aID : tallies.keySet()) {
            totalCount += tallies.get(aID);
        }

        if (totalCount == 0) {
            totalCount++; // avoid divide by zero
        }
        return (count/totalCount * 100 >= INCLUSION_THRESHOLD);
        }
}
