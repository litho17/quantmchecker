package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.ArrayList;

public class TCResult {

    private String name;

    private String value;

    // user can either give us a string value all at once, or incrementally add
    // values to a List
    private ArrayList<Component> results;

    // Little helper class so we can use a list instead of LinkedHashMap (which is vulnerable) for storing result components
    class Component {

        String key;

        String val;

        Component(String k, String v) {
            key = k;
            val = v;
        }
    }

    public TCResult(String name, String value) {
        this.name = name;
        this.value = value;
    }

    public TCResult(String name) {
        this.name = name;
        // value will be set by calling addResult
        this.value = null;
        this.results = new ArrayList<Component>();
    }

    public String getName() {
        return name;
    }

    public String getValue() {
        if (value == null) {
            String lineSeparator = System.lineSeparator();
            @Inv("= builder (+ c52 c53 c54 c55)") StringBuilder builder = new StringBuilder();
            for (Component c : results) {
                c52: builder.append(c.key);
                c53: builder.append(": ");
                c54: builder.append(c.val);
                c55: builder.append(lineSeparator);
            }
            value = builder.toString();
        }
        return value;
    }

    @Summary({"this.results", "-1"})
    public void removeResult() {
        results.remove(results.size() - 1);
    }

    @Summary({"this.results", "1"})
    public void addResult(String key, int val) {
        addResultHelper(val, key);
    }

    @Summary({"this.results", "1"})
    public void addResult(String key, double val) {
        results.add(new Component(key, Double.toString(val)));
    }

    @Summary({"this.results", "1"})
    public void addResult(String key, String val) {
        results.add(new Component(key, val));
    }

    @Summary({"this.results", "1"})
    private void addResultHelper(int val, String key) {
        results.add(new Component(key, Integer.toString(val)));
    }
}
