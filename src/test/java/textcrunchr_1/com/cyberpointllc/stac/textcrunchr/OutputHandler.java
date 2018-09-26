package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import plv.colorado.edu.quantmchecker.qual.Summary;
import textcrunchr_1.com.cyberpointllc.stac.sort.DefaultComparator;
import textcrunchr_1.com.cyberpointllc.stac.sort.Sorter;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

//
public abstract class OutputHandler {

    protected Map<String, List<TCResult>> results = new HashMap<String, List<TCResult>>();

    protected String outputForm;

    protected Sorter<String> sorter = new Sorter(DefaultComparator.STRING);

    protected Map<String, String> namesToPaths = new HashMap<String, String>();

    protected List<String> sortedFiles;

    @Summary({"this.results", "1"})
    public void addResult(String filename, TCResult tcr) {
        addResultHelper(tcr, filename);
    }

    public void conclude() throws OutputHandlerException {
        for (String file : results.keySet()) {
            namesToPaths.put(Paths.get(file).getFileName().toString(), file);
        }
        sortedFiles = sorter.sort(namesToPaths.keySet());
        do_conclude();
    }

    protected abstract void do_conclude() throws OutputHandlerException;

    @Summary({"Unverified method return"})
    private void addResultHelper(TCResult tcr, String filename) {
        if (results.containsKey(filename)) {
            List<TCResult> list = results.get(filename);
            list.add(tcr);
        } else {
            List<TCResult> newlist = new ArrayList<TCResult>();
            newlist.add(tcr);
            results.put(filename, newlist);
        }
    }
}
