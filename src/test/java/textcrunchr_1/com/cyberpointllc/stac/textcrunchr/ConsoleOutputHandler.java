package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.cyberpointllc.stac.template.TemplateEngine;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class ConsoleOutputHandler extends OutputHandler {

    public void do_conclude() {
        TemplateEngine tp = new TemplateEngine("    {{name}}\n{{output}}");
        @InvUnk("Complex loop") Map<String, String> templateMap = new HashMap<String, String>();
        String filename;
        Iterator<String> it1 = sortedFiles.iterator();
        TCResult result;
        while (it1.hasNext()) {
            c23: filename = it1.next();
            String path = namesToPaths.get(filename);
            System.out.println("        File " + filename + ": ");
            List<TCResult> sampleResults = results.get(path);
            Iterator<TCResult> it2 = sampleResults.iterator();
            while (it2.hasNext()) {
                c29: result = it2.next();
                c30: templateMap.put("name", result.getName());
                c31: templateMap.put("output", result.getValue());
                String output = tp.replaceTags(templateMap);
                System.out.println(output);
                templateMap.clear();
            }
            System.out.println("________________________");
        }
    }
}
