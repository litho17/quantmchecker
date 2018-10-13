package airplan_1.edu.cyberapex.flightplanner.guide;

import airplan_1.edu.cyberapex.flightplanner.framework.Airline;
import airplan_1.edu.cyberapex.flightplanner.framework.Flight;
import airplan_1.edu.cyberapex.flightplanner.framework.RouteMap;
import airplan_1.edu.cyberapex.flightplanner.store.AirDatabase;
import airplan_1.edu.cyberapex.template.TemplateEngine;
import airplan_1.edu.cyberapex.server.WebSessionService;
import airplan_1.edu.cyberapex.server.guide.HttpGuideResponse;
import airplan_1.edu.cyberapex.server.guide.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import airplan_1.edu.cyberapex.template.TemplateEngineBuilder;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;

import java.net.HttpURLConnection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * This handler allows a user to change all the flight's information except the origin
 * and the destination.
 */
public class EditFlightGuide extends AirGuide {
    protected static final String PATH = "/edit_flight";
    private static final String TITLE = "Edit Flight Path";
    private static final String DELETE_FIELD = "delete";
    private static final String COST_FIELD = "cost";
    private static final String DISTANCE_FIELD = "distance";
    private static final String TIME_FIELD = "time";
    private static final String CREW_FIELD = "crewMembers";
    private static final String WEIGHT_FIELD = "weightCapacity";
    private static final String PASSENGER_FIELD = "passengerCapacity";

    private static final TemplateEngine ENGINE = new TemplateEngineBuilder().defineText("<form action=\"#\" method=\"post\" enctype=\"multipart/form-data\" acceptcharset=\"UTF-8\">" +
            "    <input type=\"submit\" value=\"Delete Flight\" name=\"" + DELETE_FIELD + "\" id=\"delete\" />" +
            "</form>" +
            "<form action=\"#\" method=\"post\" enctype=\"multipart/form-data\" acceptcharset=\"UTF-8\">" +
            "    <p> Origin: {{origin}}</p>" +

            "    <p> Destination: {{dest}}</p>" +

            "    {{flightData}}<br>" +

            "    <input type=\"submit\" value=\"Submit\" name=\"submit\" id=\"submit\"/>" +
            "    <br/>" +
            "</form>").generateTemplateEngine();

    private static final Set<String> ALL_FIELDS = new HashSet<>();

    static {
        ALL_FIELDS.add(DELETE_FIELD);
        ALL_FIELDS.add(COST_FIELD);
        ALL_FIELDS.add(DISTANCE_FIELD);
        ALL_FIELDS.add(TIME_FIELD);
        ALL_FIELDS.add(CREW_FIELD);
        ALL_FIELDS.add(WEIGHT_FIELD);
        ALL_FIELDS.add(PASSENGER_FIELD);
    }

    public EditFlightGuide(AirDatabase db, WebSessionService webSessionService) {
        super(db, webSessionService);
    }

    private String getContents(Flight flight) {
        Map<String, String> contentsDictionary = new HashMap<>();
        contentsDictionary.put("origin", flight.obtainOrigin().getName());
        contentsDictionary.put("dest", flight.grabDestination().getName());
        contentsDictionary.put("flightData", generateFlightDataHTML(flight));
        return ENGINE.replaceTags(contentsDictionary);
    }

    @Override
    public String getPath() {
        return PATH;
    }


    private String generateFlightDataHTML(Flight flight) {
        StringBuilder stringBuilder = new StringBuilder();

        // add the distance input
        String distance = Integer.toString(flight.grabDistance());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(DISTANCE_FIELD, "Distance", distance));

        // add the cost input
        String cost = Integer.toString(flight.takeFuelCosts());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(COST_FIELD, "Cost", cost));

        // add the time input
        String time = Integer.toString(flight.getTravelTime());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(TIME_FIELD, "Travel Time", time));

        // add the number of crew members input
        String crew = Integer.toString(flight.pullNumCrewMembers());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(CREW_FIELD, "Number of Crew Members", crew));

        // add the weight capacity input
        String weight = Integer.toString(flight.getWeightLimit());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(WEIGHT_FIELD, "Weight Capacity", weight));

        // add the passenger capacity input
        String passengers = Integer.toString(flight.getPassengerLimit());
        stringBuilder.append(AddFlightGuide.pullFlightAttributeHTML(PASSENGER_FIELD, "Number of Passengers", passengers));

        return stringBuilder.toString();
    }

    /**
     * @param remainingPath with syntax: /(route map id)/(airport id)/(flight id)
     * @param airline       currently authenticated airline
     * @return Pair containing matched flight and routeMap from the URL
     */
    private Pair<Flight, RouteMap> getRouteMapFlightPairFromPath(String remainingPath, Airline airline) throws NumberFormatException {
        // URL structure - /edit_flight/<route map id>/<origin id>/<flight id>
        String[] urlSplit = remainingPath.split("/");

        if (urlSplit.length == 4) {
            RouteMap routeMap = airline.getRouteMap(Integer.parseInt(urlSplit[1]));

            if (routeMap != null) {
                return getRouteMapFlightPairFromPathFunction(urlSplit[3], routeMap);
            }
        }

        return new ImmutablePair<>(null, null);
    }

    private Pair<Flight, RouteMap> getRouteMapFlightPairFromPathFunction(String s, RouteMap routeMap) {
        Flight flight = routeMap.fetchFlight(Integer.parseInt(s));
        return new ImmutablePair<>(flight, routeMap);
    }

    @Override
    protected HttpGuideResponse handlePull(HttpExchange httpExchange, String remainingPath, Airline airline) {
        try {
            Pair<Flight, RouteMap> flightRouteMapPair = getRouteMapFlightPairFromPath(remainingPath, airline);

            Flight flight = flightRouteMapPair.getLeft();

            if (flight == null) {
                return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "This flight does not exist.");
            }

            return getTemplateResponse(TITLE, getContents(flight), airline);
        } catch (NumberFormatException e) {
            return fetchTemplateErrorResponse("Error while parsing the route map id. " + e.getMessage(), airline);
        } catch (NullPointerException e) {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "Unable to parse the URL");
        }

    }

    @Override
    protected HttpGuideResponse handlePost(HttpExchange httpExchange, String remainingPath, Airline airline) {
        try {
            Pair<Flight, RouteMap> flightRouteMapPair = getRouteMapFlightPairFromPath(remainingPath, airline);

            Flight flight = flightRouteMapPair.getLeft();
            RouteMap routeMap = flightRouteMapPair.getRight();

            if (flight == null) {
                return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "This flight does not exist.");
            }

            Map<String, List<String>> data = MultipartHelper.fetchMultipartValues(httpExchange, ALL_FIELDS);

            if (data.containsKey(DELETE_FIELD)) {
                routeMap.deleteFlight(flight);
            } else {
                if (data.containsKey(DISTANCE_FIELD)) {
                    String distanceStr = data.get(DISTANCE_FIELD).get(0);
                    if (!distanceStr.isEmpty()) {
                        handlePostUtility(flight, distanceStr);
                    }
                }

                if (data.containsKey(COST_FIELD)) {
                    String costStr = data.get(COST_FIELD).get(0);
                    if (!costStr.isEmpty()) {
                        int newCost = Integer.parseInt(costStr);
                        flight.defineFuelCosts(newCost);
                    }
                }

                if (data.containsKey(TIME_FIELD)) {
                    handlePostTarget(flight, data);
                }

                if (data.containsKey(CREW_FIELD)) {
                    String crewStr = data.get(CREW_FIELD).get(0);
                    if (!crewStr.isEmpty()) {
                        handlePostGuide(flight, crewStr);
                    }
                }

                if (data.containsKey(WEIGHT_FIELD)) {
                    handlePostAdviser(flight, data);
                }

                if (data.containsKey(PASSENGER_FIELD)) {
                    String passengerStr = data.get(PASSENGER_FIELD).get(0);
                    if (!passengerStr.isEmpty()) {
                        int passengers = Integer.parseInt(passengerStr);
                        flight.definePassengerLimit(passengers);
                    }
                }
            }

            return getDefaultRedirectResponse();
        } catch (NumberFormatException e) {
            return fetchTemplateErrorResponse("Unable to parse number from string. " + e.getMessage(), airline);
        } catch (NullPointerException e) {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, "Unable to parse the URL");
        }
    }

    private void handlePostAdviser(Flight flight, Map<String, List<String>> data) {
        String weightStr = data.get(WEIGHT_FIELD).get(0);
        if (!weightStr.isEmpty()) {
            handlePostAdviserWorker(flight, weightStr);
        }
    }

    private void handlePostAdviserWorker(Flight flight, String weightStr) {
        int weight = Integer.parseInt(weightStr);
        flight.fixWeightLimit(weight);
    }

    private void handlePostGuide(Flight flight, String crewStr) {
        int numCrewMembers = Integer.parseInt(crewStr);
        flight.fixNumCrewMembers(numCrewMembers);
    }

    private void handlePostTarget(Flight flight, Map<String, List<String>> data) {
        String timeStr = data.get(TIME_FIELD).get(0);
        if (!timeStr.isEmpty()) {
            handlePostTargetGuide(flight, timeStr);
        }
    }

    private void handlePostTargetGuide(Flight flight, String timeStr) {
        int travelTime = Integer.parseInt(timeStr);
        flight.setTravelTime(travelTime);
    }

    private void handlePostUtility(Flight flight, String distanceStr) {
        int newDistance = Integer.parseInt(distanceStr);
        flight.setDistance(newDistance);
    }
}
