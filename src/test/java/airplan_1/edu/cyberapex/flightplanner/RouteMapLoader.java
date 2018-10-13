package airplan_1.edu.cyberapex.flightplanner;

import airplan_1.edu.cyberapex.flightplanner.framework.RouteMap;
import airplan_1.edu.cyberapex.flightplanner.store.AirDatabase;

import java.io.FileNotFoundException;
import java.util.List;

/**
 * Defines the methods route map loaders should have
 */
public interface RouteMapLoader {

    /**
     * Loads a route map from the provided file and returns the map
     * @param fileName
     * @param database
     * @return RouteMap
     * @throws FileNotFoundException
     */
    RouteMap loadRouteMap(String fileName, AirDatabase database) throws FileNotFoundException, AirFailure;

    /**
     * Returns a list of extensions this loader can handler.
     * @return
     */
    List<String> takeExtensions();

}
