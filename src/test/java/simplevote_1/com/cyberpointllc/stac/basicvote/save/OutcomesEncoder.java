package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class OutcomesEncoder extends Serializer<SurveyOutcomes> {

    @Override
    public void serialize(DataOutput out, SurveyOutcomes outcomes) throws IOException {
        outcomes.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public SurveyOutcomes deserialize(DataInput in, int available) throws IOException {
        Map<String, Map<String, Integer>> outcomes = new HashMap<>();

        String outcomesId = in.readUTF();
        String timestamp = in.readUTF();
        String surveyId = in.readUTF();
        int eligibleVoters = in.readInt();
        int participatingVoters = in.readInt();
        int numIssues = in.readInt();
        for (int p = 0; p < numIssues; p++){
            Map<String, Integer> tally = new HashMap<>();
            String qId = in.readUTF();
            int numReplies = in.readInt();
            for (int j = 0; j < numReplies; j++){
                String aId = in.readUTF();
                Integer count = in.readInt();
                tally.put(aId, count);
            }
            outcomes.put(qId, tally);
        }
        return new SurveyOutcomes(outcomesId, timestamp, surveyId, eligibleVoters, participatingVoters, outcomes);
    }
}
