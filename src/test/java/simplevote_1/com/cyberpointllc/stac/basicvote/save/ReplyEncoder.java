package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;


public class ReplyEncoder extends Serializer<Reply> {

    @Override
    public void serialize(DataOutput out, Reply reply) throws IOException {
        reply.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public Reply deserialize(DataInput in, int available) throws IOException {
        IssueEncoder issueEncoder = new IssueEncoder();
        Issue issue = issueEncoder.deserialize(in, available);
        String replyId = in.readUTF();
        int countOfChoiceIds = in.readInt();
        Reply reply;
        Set<String> choiceIds = new HashSet<>();
        String textReply = "";
        if (countOfChoiceIds >= 0) {
            for (int a = 0; a < countOfChoiceIds; a++) {
                choiceIds.add(in.readUTF());
            }

        } else {
            textReply = in.readUTF();
        }

        String issueId = issue.grabIssueId();

        if (countOfChoiceIds >= 0) {
            reply = new Reply(replyId, issue, issueId, choiceIds);
        } else {
            reply = new Reply(replyId, issue, issueId, textReply);
        }

        return reply;
    }
}