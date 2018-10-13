package simplevote_1.com.cyberpointllc.stac.template;

import java.util.HashMap;
import java.util.Map;

public class Link implements Templated {
    private final Map<String, String> templateMap;

    public Link(String url, String name) {
        templateMap = new HashMap<>();
        templateMap.put("linkurl", url);
        templateMap.put("linkname", name);
    }

    public String fetchName() {
        return templateMap.get("linkname");
    }

    public String fetchUrl() {
        return templateMap.get("linkurl");
    }

    public Map<String, String> getTemplateMap() {
        return templateMap;
    }
}
