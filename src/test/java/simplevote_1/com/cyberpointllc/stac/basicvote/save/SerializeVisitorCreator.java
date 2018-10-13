package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import java.io.DataOutput;

public class SerializeVisitorCreator {
    private DataOutput out;

    public SerializeVisitorCreator assignOut(DataOutput out) {
        this.out = out;
        return this;
    }

    public SerializeVisitor formSerializeVisitor() {
        return new SerializeVisitor(out);
    }
}