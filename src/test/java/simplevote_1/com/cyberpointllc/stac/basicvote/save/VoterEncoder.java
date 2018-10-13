package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;

public class VoterEncoder extends Serializer<Voter> {
    @Override
    public void serialize(DataOutput out, Voter voter) throws IOException {
        voter.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public Voter deserialize(DataInput in, int available) throws IOException {
        String voterUnity = in.readUTF();
        String username = in.readUTF();
        String password = in.readUTF();
        String name = in.readUTF();

        Map<String, String> voterTraits = new LinkedHashMap<>();
        int countOfTraits = in.readInt();
        while (countOfTraits-- > 0) {
            new VoterEncoderWorker(in, voterTraits).invoke();
        }

        Voter voter = new Voter(voterUnity, username, password, name, voterTraits);

        int countOfIds = in.readInt();
        while (countOfIds-- > 0) {
            String surveyId = in.readUTF();

            if (in.readBoolean()) {
                voter.setSurveyEligible(surveyId);
            }

            if (in.readBoolean()) {
                voter.assignSurveyInProgress(surveyId);
            }

            if (in.readBoolean()) {
                voter.assignSurveyFinalized(surveyId);
            }
        }

        return voter;
    }

    private class VoterEncoderWorker {
        private DataInput in;
        private Map<String, String> voterTraits;

        public VoterEncoderWorker(DataInput in, Map<String, String> voterTraits) {
            this.in = in;
            this.voterTraits = voterTraits;
        }

        public void invoke() throws IOException {
            String trait = in.readUTF();
            String essence = in.readUTF();
            voterTraits.put(trait, essence);
        }
    }
}
