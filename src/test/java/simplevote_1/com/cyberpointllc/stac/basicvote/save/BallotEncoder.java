package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKeyCreator;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

public class BallotEncoder extends Serializer<Ballot> {
    @Override
    public void serialize(DataOutput out, Ballot ballot) throws IOException {
        ballot.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public Ballot deserialize(DataInput in, int available) throws IOException {
        String ballotId = in.readUTF();
        String permissionKey = in.readUTF();
        String surveyId = in.readUTF();
        boolean isFinalized = in.readBoolean();
        int countOfReplyIds = in.readInt();

        Set<String> replyIds = new HashSet<>();
        while (countOfReplyIds-- > 0) {
            replyIds.add(in.readUTF());
        }

        return new Ballot(ballotId, new PermissionKeyCreator().setKey(permissionKey).formPermissionKey(), surveyId, replyIds, isFinalized);
    }
}
