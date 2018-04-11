package gabfeed_1.com.cyberpointllc.stac.gabfeed.persist;

import gabfeed_1.com.cyberpointllc.stac.gabfeed.model.GabChat;
import org.mapdb.Serializer;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.Random;

public class ChatSerializer extends Serializer<GabChat> {

    private final GabDatabase db;

    public ChatSerializer(GabDatabase db) {
        this.db = db;
    }

    @Override
    public void serialize(DataOutput out, GabChat value) throws IOException {
        out.writeUTF(value.getId());
        DATE.serialize(out, value.getLastUpdated());
        Set<String> userIds = value.getUserIds();
        out.writeInt(userIds.size());
        for (String userId : userIds) {
            out.writeUTF(userId);
        }
        List<String> messageIds = value.getMessageIds();
        out.writeInt(messageIds.size());
        for (String messageId : messageIds) {
            serializeHelper(messageId, out);
        }
    }

    @Override
    public GabChat deserialize(DataInput in, int available) throws IOException {
        String id = in.readUTF();
        Date lastUpdated = DATE.deserialize(in, available);
        int numberOfUsers = in.readInt();
        @Inv("i+<self>=+c51-c50") Set<String> userIds = new  LinkedHashSet(numberOfUsers);
        for (int i = 0; i < numberOfUsers; ) {
            Random randomNumberGeneratorInstance = new  Random();
            for (; i < numberOfUsers && randomNumberGeneratorInstance.nextDouble() < 0.5; ) {
                c50: for (; i < numberOfUsers && randomNumberGeneratorInstance.nextDouble() < 0.5; i++) {
                    c51: deserializeHelper(userIds, in);
                }
            }
        }
        int numberOfMessages = in.readInt();
        @Inv("j+<self>=+c62-c61") List<String> messageIds = new  ArrayList(numberOfMessages);
        for (int j = 0; j < numberOfMessages; ) {
            Random randomNumberGeneratorInstance = new  Random();
            for (; j < numberOfMessages && randomNumberGeneratorInstance.nextDouble() < 0.5; ) {
                c61: for (; j < numberOfMessages && randomNumberGeneratorInstance.nextDouble() < 0.5; j++) {
                    c62: deserializeHelper1(messageIds, in);
                }
            }
        }
        return new  GabChat(db, id, userIds, lastUpdated, messageIds);
    }

    private void serializeHelper(String messageId, DataOutput out) throws IOException {
        out.writeUTF(messageId);
    }

    @Summary({"userIds", "1"})
    private void deserializeHelper(@Inv("+<self>=+c75") Set<String> userIds, DataInput in) throws IOException {
        c75: userIds.add(in.readUTF());
    }

    @Summary({"messageIds", "1"})
    private void deserializeHelper1(@Inv("+<self>=+c79") List<String> messageIds, DataInput in) throws IOException {
        c79: messageIds.add(in.readUTF());
    }
}
