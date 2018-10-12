package calculator_1.com.cyberpointllc.stac.netcontroller.persist;

import calculator_1.com.cyberpointllc.stac.netcontroller.User;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

public class UserDigitizer extends Serializer<User> {

    @Override
    public void serialize(DataOutput out, User user) throws IOException {

        out.writeUTF(user.takeEmpty());
        out.writeUTF(user.grabUsername());
        out.writeUTF(user.grabPassword());

    }

    @Override
    public User deserialize(DataInput in, int available) throws IOException {

        String empty = in.readUTF();
        String username = in.readUTF();
        String password = in.readUTF();

        return new User(empty, username, password);
    }
}
