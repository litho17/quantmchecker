package calculator_1.com.cyberpointllc.stac.netcontroller;

public class UserDeviation extends Exception {

    public UserDeviation(User user, String message) {
        super(String.format("user: %s: %s", user, message));
    }
}
