package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.cyberpointllc.stac.hashmap.HashMap;
import textcrunchr_1.com.cyberpointllc.stac.sort.DefaultComparator;
import textcrunchr_1.com.cyberpointllc.stac.sort.Sorter;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

//
public abstract class OutputHandler {

    protected Map<String, List<TCResult>> results = new  HashMap<String, List<TCResult>>();

    protected String outputForm;

    protected Sorter<String> sorter = new  Sorter(DefaultComparator.STRING);

    protected @InvUnk("z") Map<String, String> namesToPaths = new  HashMap<String, String>();

    protected List<String> sortedFiles;

    @Summary({"results", "1"})
    public void addResult(String filename, TCResult tcr) {
        addResultHelper(tcr, filename);
    }

    public void conclude() throws OutputHandlerException {
        concludeHelper();
    }

    protected abstract void do_conclude() throws OutputHandlerException;

    private void addResultHelper(TCResult tcr, String filename) {
        if (results.containsKey(filename)) {
            List<TCResult> list = results.get(filename);
            list.add(tcr);
        } else {
            List<TCResult> newlist = new  ArrayList<TCResult>();
            newlist.add(tcr);
            c44: results.put(filename, newlist);
        }
    }

    private void concludeHelper() throws OutputHandlerException {
        c49: for (String file : results.keySet()) {
            c50: namesToPaths.put(Paths.get(file).getFileName().toString(), file);
        }
        sortedFiles = sorter.sort(namesToPaths.keySet());
        do_conclude();
    }
}
