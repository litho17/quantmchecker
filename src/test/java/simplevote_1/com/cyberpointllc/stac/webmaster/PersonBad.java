package simplevote_1.com.cyberpointllc.stac.webmaster;

public class PersonBad extends Exception {

    public PersonBad(Person person, String message) {
        super(String.format("user: %s: %s", person, message));
    }
}
