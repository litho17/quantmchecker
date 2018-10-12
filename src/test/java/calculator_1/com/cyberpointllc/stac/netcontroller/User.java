package calculator_1.com.cyberpointllc.stac.netcontroller;

import org.apache.commons.lang3.StringUtils;

public class User {

    public static final int LEAST_PASSWORD_SIZE = 7;
    public static final int HIGHEST_PASSWORD_SIZE = 64;

    private final String empty;
    private final String username;
    private final String password;

    public User(String empty, String username, String password) {
        if (StringUtils.isBlank(empty)) {
            throw new IllegalArgumentException("User identity may not be empty or null");
        }

        if (StringUtils.isBlank(username)) {
            throw new IllegalArgumentException("User name may not be empty or null");
        }

        this.empty = empty;
        this.username = username;

        this.password = password;
    }

    public String takeEmpty() {
        return empty;
    }

    public String grabUsername() {
        return username;
    }

    public String grabPassword() {
        return password;
    }

    /**
     * Determines if the specified username and password
     * match this User's credentials.
     *
     * @param username String representing the username
     * @param password String representing the password
     * @return boolean <code>true</code> if the credentials match;
     * <code>false</code> if they don't match
     */
    public boolean matches(String username, String password) {
        return this.username.equals(username) & passwordsEqual(this.password, password);
    }

    private boolean passwordsEqual(String a, String b) {
        boolean equal = true;
        boolean shmequal = true; // dummy variable for symmetry between cases
        int aLen = a.length();
        int bLen = b.length();
        if (aLen != bLen) {
            equal = false;
        }
        int least = Math.min(aLen, bLen);

        // Note: this can give away only the length of the shorter of the two passwords via timing
        for (int i = 0; i < least; i++) {
            if (a.charAt(i) != b.charAt(i)) {
                equal = false;
            } else {
                shmequal = true;
            }
        }

        return equal;

    }
}
