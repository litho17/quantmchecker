package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

// import com.cyberpointllc.stac.hashmap.HashMap;
import plv.colorado.edu.quantmchecker.qual.Inv;
import textcrunchr_1.com.cyberpointllc.stac.sort.DefaultComparator;
import textcrunchr_1.com.cyberpointllc.stac.sort.Sorter;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

//
public abstract class OutputHandler {

    protected @Inv({"INPUTINPUT+<self>=+Driver21+Driver23+Driver25+Driver27+Driver29-Driver16"}) Map<String, List<TCResult>> results = new HashMap<String, List<TCResult>>();

    protected String outputForm;

    protected Sorter<String> sorter = new  Sorter(DefaultComparator.STRING);

    protected Map<String, String> namesToPaths = new  HashMap<String, String>();

    protected List<String> sortedFiles;

    @Summary({"results", "1"}) public void addResult(String filename, TCResult tcr) {
        addResultHelper(tcr, filename);
    }

    @Summary({"namesToPaths", "1"}) public void conclude() throws OutputHandlerException {
        concludeHelper();
    }

    protected abstract void do_conclude() throws OutputHandlerException;

    @Summary({"results", "1"})
    private void addResultHelper(TCResult tcr, String filename) {
        // @Inv("+<self>=+OutputHandler42+OutputHandler44") List<TCResult> newlist;
        if (results.containsKey(filename)) {
            @Inv("+<self>=+OutputHandler42+OutputHandler44") List<TCResult> newlist = results.get(filename);
            OutputHandler42: newlist.add(tcr);
        } else {
            @Inv("+<self>=+OutputHandler42+OutputHandler44") List<TCResult> newlist = new  ArrayList<TCResult>();
            OutputHandler44: newlist.add(tcr);
            results.put(filename, newlist);
        }
    }

    @Summary({"namesToPaths", "1"})
    private void concludeHelper() throws OutputHandlerException {
        for (String file : results.keySet()) {
            namesToPaths.put(Paths.get(file).getFileName().toString(), file);
        }
        sortedFiles = sorter.sort(namesToPaths.keySet());
        do_conclude();
    }
}
