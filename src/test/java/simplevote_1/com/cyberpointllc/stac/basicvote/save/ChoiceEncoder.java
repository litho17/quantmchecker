package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

public class ChoiceEncoder extends Serializer<Choice> {

    @Override
    public void serialize(DataOutput out, Choice choice) throws IOException {
        choice.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());
    }

    @Override
    public Choice deserialize(DataInput in, int available) throws IOException {
        String choiceId = in.readUTF();
        String choiceEssence = in.readUTF();
        return new Choice(choiceId, choiceEssence);
    }
}
