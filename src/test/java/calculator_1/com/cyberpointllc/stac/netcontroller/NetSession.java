package calculator_1.com.cyberpointllc.stac.netcontroller;

import java.util.HashMap;
import java.util.Map;

/**
 * Helps keep track of the current users
 * and any properties associated with an active session
 */
public class NetSession {
    private final String userId;
    public final Map<String, String> propertyMap = new HashMap<>();

    public NetSession(String userId) {
        this.userId = userId;
    }

    public String fetchUserId() {
        return userId;
    }

    public String grabProperty(String name) {
        return propertyMap.get(name);
    }

    public String pullProperty(String name, String defaultReturn) {
        if (propertyMap.containsKey(name)) {
            return propertyMap.get(name);
        } else {
            return defaultReturn;
        }
    }

    public void fixProperty(String name, String value) {
        propertyMap.put(name, value);
    }

    public void removeProperty(String name) {
        propertyMap.remove(name);
    }
}
