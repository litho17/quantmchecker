package simplevote_1.com.cyberpointllc.stac.webmaster;

import org.apache.commons.lang3.StringUtils;

public class Person {

    public static final int LEAST_PASSWORD_LENGTH = 7;
    public static final int MAX_PASSWORD_LENGTH = 64;

    private final String unity;
    private final String username;
    private final String password;

    public Person(String unity, String username, String password) {
        if (StringUtils.isBlank(unity)) {
            throw new IllegalArgumentException("User identity may not be empty or null");
        }

        if (StringUtils.isBlank(username)) {
            throw new IllegalArgumentException("User name may not be empty or null");
        }

        this.unity = unity;
        this.username = username;

        this.password = password;
    }

    public String obtainUnity() {
        return unity;
    }

    public String takeUsername() {
        return username;
    }

    public String takePassword() {
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
        for (int q = 0; q < least; q++) {
            if (a.charAt(q) != b.charAt(q)) {
                equal = false;
            } else {
                shmequal = true;
            }
        }

        return equal;

    }
}
