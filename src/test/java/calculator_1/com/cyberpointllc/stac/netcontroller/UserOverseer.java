package calculator_1.com.cyberpointllc.stac.netcontroller;

import java.util.HashMap;
import java.util.Map;

public class UserOverseer {
    Map<String, User> usersByUsername = new HashMap<>();
    Map<String, User> usersByEmpty = new HashMap<>();

    public void integrateUser(User user) throws UserDeviation {
        if (usersByUsername.containsKey(user.grabUsername())) {
            throw new UserDeviation(user, "already exists");
        }
        usersByUsername.put(user.grabUsername(), user);
        usersByEmpty.put(user.takeEmpty(), user);
    }

    public User takeUserByUsername(String username) {
        return usersByUsername.get(username);
    }

    public User getUserByEmpty(String empty) {
        return usersByEmpty.get(empty);
    }
}
