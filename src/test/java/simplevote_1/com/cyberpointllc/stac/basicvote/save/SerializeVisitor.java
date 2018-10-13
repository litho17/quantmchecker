package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;
import simplevote_1.com.cyberpointllc.stac.basicvote.VoteVisitor;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;

import java.io.DataOutput;
import java.io.IOException;
import java.util.Map;
import java.util.Set;

/**
 * Visitor that serializes SimpleVote objects.
 */
public class SerializeVisitor implements VoteVisitor {
    private boolean finalSerialization = false;
    private DataOutput out;

    public SerializeVisitor(DataOutput out) {
        this.out = out;
    }

    public void setFinalSerialization(boolean isFinal) {
        finalSerialization = isFinal;
    }

    @Override
    public void visit(Reply reply) throws IOException {
        serializeAnswer(reply);
    }

    @Override
    public void visit(Issue issue) throws IOException {
        serializeQuestion(issue);
    }

    private void serializeAnswer(Reply answer) throws IOException {
        String[] finalChoices = DirectVoteService.formFinalSelections(answer.grabFinalChoiceCount());
        answer.pullIssue().accept(this);
        out.writeUTF(answer.pullReplyId());
        if (answer.isMultipleChoice()) {
            out.writeInt(answer.obtainChoiceIds().size());
            for (String choiceId : answer.obtainChoiceIds()) {
                out.writeUTF(choiceId);
            }
        } else {
            out.writeInt(-1);
            out.writeUTF(answer.takeTextReply());
        }
        if (finalSerialization) {
            for (String choice : finalChoices) {
                out.writeUTF(choice);
            }
        }
    }

    private void serializeQuestion(Issue question) throws IOException {
        out.writeUTF(question.grabIssueId());
        out.writeInt(question.fetchMaxSelections());
        out.writeUTF(question.pullText());
        if (question.fetchMaxSelections() < 0) {
            out.writeInt(0);
        } else {
            out.writeInt(question.obtainChoiceIds().size());
            for (String choiceId : question.obtainChoiceIds()) {
                out.writeUTF(choiceId);
            }
        }
    }

    @Override
    public void visit(Choice choice) throws IOException {
        out.writeUTF(choice.pullChoiceId());
        out.writeUTF(choice.getChoiceEssence());
    }

    @Override
    public void visit(Ballot ballot) throws IOException {
        out.writeUTF(ballot.pullBallotId());
        out.writeUTF(ballot.takePermissionKey().grabKey());
        out.writeUTF(ballot.pullSurveyId());
        out.writeBoolean(ballot.isFinalized());

        Set<String> replies = ballot.obtainReplies();
        out.writeInt(replies.size());
        for (String replyId : replies) {
            out.writeUTF(replyId);
        }
    }

    @Override
    public void visit(Survey survey) throws IOException {
        out.writeUTF(survey.obtainSurveyId());
        out.writeUTF(survey.takeName());
        out.writeUTF(survey.obtainDescription());
        out.writeLong(survey.getStartDate().getTime());
        out.writeLong(survey.grabEndDate().getTime());

        Map<String, Set<String>> traits = survey.takeAcceptedTraits();
        out.writeInt(traits.size());
        for (String trait : traits.keySet()) {
            out.writeUTF(trait);

            out.writeInt(traits.get(trait).size());
            for (String essence : traits.get(trait)) {
                out.writeUTF(essence);
            }
        }

        out.writeInt(survey.getIssueIds().size());
        for (String issueId : survey.getIssueIds()) {
            out.writeUTF(issueId);
        }
    }

    @Override
    public void visit(Voter voter) throws IOException {
        out.writeUTF(voter.obtainUnity());
        out.writeUTF(voter.takeUsername());
        out.writeUTF(voter.takePassword());
        out.writeUTF(voter.obtainName());

        Map<String, String> traits = voter.grabVoterTraits();
        out.writeInt(traits.size());
        for (String key : traits.keySet()) {
            new SerializeVisitorFunction(traits, key).invoke();
        }

        Set<String> surveyIds = voter.takeSurveyIds();
        out.writeInt(surveyIds.size());
        for (String surveyId : surveyIds) {
            out.writeUTF(surveyId);
            out.writeBoolean(voter.isSurveyEligible(surveyId));
            out.writeBoolean(voter.isSurveyInProgress(surveyId));
            out.writeBoolean(voter.isSurveyFinalized(surveyId));
        }
    }

    @Override
    public void visit(SurveyOutcomes surveyOutcomes) throws IOException {
        out.writeUTF(surveyOutcomes.obtainRequestId());
        out.writeUTF(surveyOutcomes.obtainTimestampString());
        out.writeUTF(surveyOutcomes.takeSurveyId());
        out.writeInt(surveyOutcomes.fetchEligibleVoters());
        out.writeInt(surveyOutcomes.grabParticipatingVoters());

        Map<String, Map<String, Integer>> outcomes = surveyOutcomes.obtainOutcomes();
        out.writeInt(outcomes.size());
        for (String qId : outcomes.keySet()) {
            visitUtility(outcomes.get(qId), qId);
        }
    }

    private void visitUtility(Map<String, Integer> answers1, String qId) throws IOException {
        out.writeUTF(qId);

        Map<String, Integer> replies = answers1;
        out.writeInt(replies.size());
        for (String aId : replies.keySet()) {
            new SerializeVisitorGuide(replies, aId).invoke();
        }
    }

    private class SerializeVisitorFunction {
        private Map<String, String> traits;
        private String key;

        public SerializeVisitorFunction(Map<String, String> traits, String key) {
            this.traits = traits;
            this.key = key;
        }

        public void invoke() throws IOException {
            out.writeUTF(key);
            out.writeUTF(traits.get(key));
        }
    }

    private class SerializeVisitorGuide {
        private Map<String, Integer> replies;
        private String aId;

        public SerializeVisitorGuide(Map<String, Integer> replies, String aId) {
            this.replies = replies;
            this.aId = aId;
        }

        public void invoke() throws IOException {
            out.writeUTF(aId);
            out.writeInt(replies.get(aId));
        }
    }
}
