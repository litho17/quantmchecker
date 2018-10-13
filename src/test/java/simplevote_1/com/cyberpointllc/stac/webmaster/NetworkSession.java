package simplevote_1.com.cyberpointllc.stac.webmaster;

import java.util.HashMap;
import java.util.Map;

/**
 * Helps keep track of the current users
 * and any properties associated with an active session
 */
public class NetworkSession {
    private final String personId;
    private final Map<String, String> propertyMap = new HashMap<>();

    public NetworkSession(String personId) {
        this.personId = personId;
    }

    public String pullPersonId() {
        return personId;
    }

    public String fetchProperty(String name) {
        return propertyMap.get(name);
    }

    public String obtainProperty(String name, String defaultReturn) {
        if (propertyMap.containsKey(name)) {
            return propertyMap.get(name);
        } else {
            return defaultReturn;
        }
    }

    public void setProperty(String name, String essence) {
        propertyMap.put(name, essence);
    }

    public void removeProperty(String name) {
        propertyMap.remove(name);
    }
}
