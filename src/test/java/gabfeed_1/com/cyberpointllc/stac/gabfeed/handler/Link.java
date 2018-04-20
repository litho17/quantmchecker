package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.hashmap.HashMap;
import gabfeed_1.com.cyberpointllc.stac.template.Templated;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.Map;

public class Link implements Templated {

    private final Map<String, String> templateMap;

    @Summary({"this.templateMap", "2"})
    public Link(String url, String name) {
        templateMap = new  HashMap();
        templateMap.put("linkurl", url);
        templateMap.put("linkname", name);
    }

    public String getName() {
        return templateMap.get("linkname");
    }

    public String getUrl() {
        return templateMap.get("linkurl");
    }

    public Map<String, String> getTemplateMap() {
        return templateMap;
    }
}
