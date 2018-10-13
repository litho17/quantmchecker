package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class IssueEncoder extends Serializer<Issue> {

    @Override
    public void serialize(DataOutput out, Issue issue) throws IOException {
        issue.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public Issue deserialize(DataInput in, int available) throws IOException {
        String issueId = in.readUTF();
        int maxSelections = in.readInt();
        String text = in.readUTF();

        List<String> choiceIds = new ArrayList<>();
        int countOfChoiceIds = in.readInt();
        if (countOfChoiceIds == 0) {
            return new Issue(issueId, text);
        } else {
            while (countOfChoiceIds-- > 0) {
                choiceIds.add(in.readUTF());
            }
            return new Issue(issueId, text, choiceIds, maxSelections);
        }
    }
}
