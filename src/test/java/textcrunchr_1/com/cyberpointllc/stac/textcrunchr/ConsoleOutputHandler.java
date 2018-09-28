package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.cyberpointllc.stac.template.TemplateEngine;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ConsoleOutputHandler extends OutputHandler {

    public void do_conclude() {
        TemplateEngine tp = new TemplateEngine("    {{name}}\n{{output}}");
        @InvUnk("Nested loop") Map<String, String> templateMap = new HashMap<String, String>();
        for (String filename : sortedFiles) {
            String path = namesToPaths.get(filename);
            System.out.println("        File " + filename + ": ");
            List<TCResult> sampleResults = results.get(path);
            for (TCResult result : sampleResults) {
                templateMap.put("name", result.getName());
                templateMap.put("output", result.getValue());
                String output = tp.replaceTags(templateMap);
                System.out.println(output);
                templateMap.clear();
            }
            System.out.println("________________________");
        }
    }
}
