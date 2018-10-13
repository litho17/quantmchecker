package simplevote_1.com.cyberpointllc.stac.webmaster;

import java.util.HashMap;
import java.util.Map;

public class PersonConductor {
    Map<String, Person> peopleByUsername = new HashMap<>();
    Map<String, Person> peopleByUnity = new HashMap<>();

    public void addPerson(Person person) throws PersonBad {
        if (peopleByUsername.containsKey(person.takeUsername())) {
            throw new PersonBad(person, "already exists");
        }
        peopleByUsername.put(person.takeUsername(), person);
        peopleByUnity.put(person.obtainUnity(), person);
    }

    public Person fetchPersonByUsername(String username) {
        return peopleByUsername.get(username);
    }

    public Person grabPersonByUnity(String unity) {
        return peopleByUnity.get(unity);
    }
}
