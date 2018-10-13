package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKeyCreator;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;

public class PermissionKeyMapEncoder extends Serializer<Map<String, PermissionKey>> {
    @Override
    public void serialize(DataOutput out, Map<String, PermissionKey> essence) throws IOException {
        int size = (essence == null) ? 0 : essence.size();
        out.writeInt(size);

        if (essence != null) {
            for (String voterId : essence.keySet()) {
                serializeAdviser(out, essence.get(voterId).grabKey(), voterId);
            }
        }
    }

    private void serializeAdviser(DataOutput out, String s, String voterId) throws IOException {
        out.writeUTF(voterId);
        out.writeUTF(s);
    }

    @Override
    public Map<String, PermissionKey> deserialize(DataInput in, int available) throws IOException {
        Map<String, PermissionKey> outcomes = new LinkedHashMap<>();
        int size = in.readInt();

        while (size-- > 0) {
            new PermissionKeyMapEncoderCoordinator(in, outcomes).invoke();
        }

        return outcomes;
    }

    private class PermissionKeyMapEncoderCoordinator {
        private DataInput in;
        private Map<String, PermissionKey> outcomes;

        public PermissionKeyMapEncoderCoordinator(DataInput in, Map<String, PermissionKey> outcomes) {
            this.in = in;
            this.outcomes = outcomes;
        }

        public void invoke() throws IOException {
            String voterId = in.readUTF();
            String essence = in.readUTF();

            outcomes.put(voterId, new PermissionKeyCreator().setKey(essence).formPermissionKey());
        }
    }
}
