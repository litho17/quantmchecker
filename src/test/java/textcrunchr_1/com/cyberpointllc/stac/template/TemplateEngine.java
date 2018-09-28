package textcrunchr_1.com.cyberpointllc.stac.template;

import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.commons.lang3.tuple.Pair;
import plv.colorado.edu.quantmchecker.qual.*;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * This engine takes a template in the form of a string and possibly a start tag
 * and end tag that define how the template identifies keys. Once an engine is
 * created, replaceTags takes a dictionary containing the template keys and
 * associated values. It outputs a string with the template keys replaced by
 * their associated values.
 * <p>
 * An example:
 * Template engine reads in "Hello, {{name}}. Good {{timeOfDay}}."
 * <p>
 * Our dictionary contains the key "name" with value "Bob" and the key
 * "timeOfDay" with value "evening".
 * <p>
 * Our output from replaceTags with this dictionary is "Hello, Bob. Good evening."
 */
public class TemplateEngine {

    private String startTag;

    private String endTag;

    private Pattern pattern;

    private String text;

    public TemplateEngine(String startTag, String endTag, String text) {
        this.startTag = startTag;
        this.endTag = endTag;
        this.pattern = Pattern.compile(startTag + ".*?" + endTag);
        this.text = text;
    }

    public TemplateEngine(String text) {
        this("\\{\\{", "\\}\\}", text);
    }

    /**
     * Creates a new String where the tags in text have been replaced with the
     * values specified in the dictionary
     *
     * @param dictionary a Map with template keys and their corresponding values
     * @return new version of text where the tags and their keys have been
     * replaced with the keys' corresponding values
     */
    public String replaceTags(Map<String, String> dictionary) {
        @InvUnk("Update not expressible with method summary") StringBuilder sb = new StringBuilder();
        replaceTagsBuilder(dictionary, sb);
        return sb.toString();
    }

    /**
     * Adds to the string builder, the template where the tags in text have been replaced with the
     * values specified in the dictionary
     *
     * @param dictionary a Map with template keys and their corresponding values
     * @param sb         The string builder to put the data in
     */
    public void replaceTagsBuilder(Map<String, String> dictionary,
                                   @Inc("= (- self i) (- (+ c104 c108 c113) (+ c110 c110))") StringBuilder sb) {
        // keep track of where we are on the text string
        int linePointer = 0;
        int startTagLength = StringEscapeUtils.unescapeJava(startTag).length();
        int endTagLength = StringEscapeUtils.unescapeJava(endTag).length();
        @Input("(and (<= matcher text) (<= text 100))") int j;
        Matcher matcher = pattern.matcher(text);
        @Inv("= (- tagsList matcher) (- c64 c62 c65)") List<Pair<Integer, Integer>> tagsList = new ArrayList();
        boolean find;
        c62: find = matcher.find();
        while (find) {
            c64: tagsList.add(Pair.of(matcher.start(), matcher.end()));
            c65: find = matcher.find();
        }
        for (int i = 0; i < tagsList.size(); ) {
            int startTagLocation = tagsList.get(i).getLeft();
            int endTagLocation = tagsList.get(i).getRight();
            // append the part of the text that doesn't have tags
            sb.append(text.substring(linePointer, startTagLocation));
            // get the dictionary key
            String key = text.substring(startTagLocation + startTagLength, endTagLocation - endTagLength).trim();
            // append the value to the text instead of the key
            sb.append(dictionary.get(key));
            linePointer = endTagLocation;
            i++;
        }
        // append the last part of the text that doesn't have tags
        sb.append(text.substring(linePointer, text.length()));
    }

    public String replaceTags(Templated templated) {
        return replaceTags(templated.getTemplateMap());
    }

    /**
     * Applies the template to each item in 'templateds' returning the string
     *
     * @param templateds the items to apply to the template
     * @param separator  the separator to put after each item
     * @return a string representing all of the templated items
     */
    public String replaceTags(@Input("(and (<= it templateds) (<= templateds 100))") List<? extends Templated> templateds, String separator) {
        @Inv("= (- sb it) (- c130 c128)") StringBuilder sb = new StringBuilder();
        Iterator<? extends Templated> it = templateds.iterator();
        while (it.hasNext()) {
            Templated templated;
            c128: templated = it.next();
            replaceTagsBuilder(templated.getTemplateMap(), sb);
            c130: sb.append(separator);
        }
        return sb.toString();
    }

    /**
     * Applies the template to each item in 'templateds' returning the string
     *
     * @param templateds the items to apply to the template
     * @return a string representing all of the templated items
     */
    public String replaceTags(List<? extends Templated> templateds) {
        return replaceTags(templateds, "");
    }
}
