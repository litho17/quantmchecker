package calculator_1.com.cyberpointllc.stac.template;

import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.commons.lang3.tuple.Pair;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.ArrayList;
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
 * 
 * An example:
 * Template engine reads in "Hello, {{name}}. Good {{timeOfDay}}."
 * 
 * Our dictionary contains the key "name" with value "Bob" and the key
 * "timeOfDay" with value "evening".
 * 
 * Our output from replaceTags with this dictionary is "Hello, Bob. Good evening."
 *
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
     * @param dictionary
     *            a Map with template keys and their corresponding values
     * @return new version of text where the tags and their keys have been
     *         replaced with the keys' corresponding values
     */
    public String replaceTags(Map<String, String> dictionary) {
        @Inv("= (- sb c c) (- (+ c79 c85 c91) c87 c87)") StringBuilder sb = new StringBuilder();
        // keep track of where we are on the text string
        int linePointer = 0;
        int startTagSize = StringEscapeUtils.unescapeJava(startTag).length();
        int endTagSize = StringEscapeUtils.unescapeJava(endTag).length();
        @Bound("+ 4 (* 3 text)") int j;
        @Iter("<= matcher text") Matcher matcher = pattern.matcher(text);
        @Inv("= (- tagsList matcher) (- c68 c66 c69)") List<Pair<Integer, Integer>> tagsList = new ArrayList<>();
        boolean find;
        c66: find = matcher.find();
        while (find) {
            c68: tagsList.add(Pair.of(matcher.start(), matcher.end()));
            c69: find = matcher.find();
        }

        for (@Iter("<= c tagsList") int c = 0; c < tagsList.size(); ) {

            int startTagEnvironment = tagsList.get(c).getLeft();
            int endTagEnvironment = tagsList.get(c).getRight();

            // append the part of the text that doesn't have tags
            c79: sb.append(text.substring(linePointer, startTagEnvironment));

            // get the dictionary key
            String code = text.substring(startTagEnvironment + startTagSize, endTagEnvironment - endTagSize).trim();

            // append the value to the text instead of the key
            c85: sb.append(dictionary.get(code));
            linePointer = endTagEnvironment;
            c87: c = c + 1;
        }

        // append the last part of the text that doesn't have tags
        c91: sb.append(text.substring(linePointer, text.length()));
        return sb.toString();
    }

    public String replaceTags(Templated templated) {
        return replaceTags(templated.fetchTemplateMap());
    }

    /**
     * Applies the template to each item in 'templateds' returning the string
     * @param templateds the items to apply to the template
     * @param separator the separator to put after each item
     *
     * @return a string representing all of the templated items
     */
    public String replaceTags(List<? extends Templated> templateds, String separator) {
        @Bound("+ (* 2 (+ text 1) templateds) (* 2 templateds) text 1") int j;
        @Iter("<= matcher text") Matcher matcher = pattern.matcher(text);
        @Inv("= (- tagsList matcher) (- c112 c110 c113)") List<Pair<Integer, Integer>> tagsList = new ArrayList<>();
        boolean find;
        c110: find = matcher.find();
        while (find) {
            c112: tagsList.add(Pair.of(matcher.start(), matcher.end()));
            c113: find = matcher.find();
        }

        @Inv("= (- sb i i) (- (+ c143 c144 c131 c137) c145 c145)") StringBuilder sb = new StringBuilder();
        for (@Iter("(and (<= i templateds) (<= c131 (* tagsList templateds)))") int i = 0; i < templateds.size(); ) {
            Templated templated = templateds.get(i);
            // keep track of where we are on the text string
            int linePointer = 0;
            int startTagSize = StringEscapeUtils.unescapeJava(startTag).length();
            int endTagSize = StringEscapeUtils.unescapeJava(endTag).length();

            for (int c = 0; c < tagsList.size(); c++) {

                int startTagEnvironment = tagsList.get(c).getLeft();
                int endTagEnvironment = tagsList.get(c).getRight();

                // append the part of the text that doesn't have tags
                c131: sb.append(text.substring(linePointer, startTagEnvironment));

                // get the dictionary key
                String code = text.substring(startTagEnvironment + startTagSize, endTagEnvironment - endTagSize).trim();

                // append the value to the text instead of the key
                c137: sb.append(templated.fetchTemplateMap().get(code));

                linePointer = endTagEnvironment;
            }

            // append the last part of the text that doesn't have tags
            c143: sb.append(text.substring(linePointer, text.length()));
            c144: sb.append(separator);
            c145: i = i + 1;
        }
        return sb.toString();
    }

    /**
     * Applies the template to each item in 'templateds' returning the string
     * @param templateds the items to apply to the template
     *
     * @return a string representing all of the templated items
     */
    public String replaceTags(List<? extends Templated> templateds) {
        return replaceTags(templateds, "");
    }
}