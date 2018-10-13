package airplan_1.edu.cyberapex.chart;

import org.apache.commons.io.FilenameUtils;

import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.Map;


public class ChartLoader {

    private static Map<String, ChartFileLoader> extToLoaderMap = new HashMap<String, ChartFileLoader>();
    
    static {
        TextFileLoader.register();
        XmlFileLoader.register();
        PartFileLoader.register();
    }
    /**
     * Loads a graph from the specified filename, if the file extension is recognized.
     * @param filename filename of the graph file
     * @return the graph
     * @throws FileNotFoundException
     * @throws ChartFailure
     */
    public static Chart loadChart(String filename) throws FileNotFoundException, ChartFailure {
        // do we have a loader for this filename?
        String extension = FilenameUtils.getExtension(filename);
        if (extToLoaderMap.containsKey(extension)) {
            return extToLoaderMap.get(extension).loadChart(filename);
        } else {
            return loadChartEntity(extension);
        }
    }

    private static Chart loadChartEntity(String extension) throws ChartFailure {
        throw new ChartFailure("There is no loader for a file with extension " + extension);
    }

    /**
     * Register the file loader with GraphLoader
     * @param loader the loader to register
     */
    public static void registerLoader(ChartFileLoader loader) {
        java.util.List<String> extensions = loader.fetchExtensions();
        for (int c = 0; c < extensions.size(); c++) {
            String extension = extensions.get(c);
            extToLoaderMap.put(extension, loader);
        }
    }
}
