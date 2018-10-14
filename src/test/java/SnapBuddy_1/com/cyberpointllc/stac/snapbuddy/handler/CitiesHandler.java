package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.LocationService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.AbstractHttpHandler;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.util.Iterator;

public class CitiesHandler extends AbstractHttpHandler {

    private static final String PATH = "/cities";

    private final LocationService locationService;

    public CitiesHandler(LocationService locationService) {
        if (locationService == null) {
            throw new  IllegalArgumentException("LocationService may not be null");
        }
        this.locationService = locationService;
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        @InvUnk("Nested lists") StringBuilder sb = new  StringBuilder();
        // Add a header line
        sb.append("City,BSSIDs\r\n");
        Iterator<Location> it1 = locationService.getLocations().iterator();
        while (it1.hasNext()) {
            Location location;
            location = it1.next();
            sb.append('"');
            sb.append(location.getCity());
            sb.append('"');
            sb.append(',');
            sb.append('"');
            boolean firstime = true;
            for (String bssid : location.getAccessPointBssids()) {
                if (firstime) {
                    firstime = false;
                } else {
                    sb.append(',');
                }
                sb.append(bssid);
            }
            sb.append('"');
            sb.append("\r\n");
        }
        return new  CSVHandlerResponse(sb.toString());
    }

    private static class CSVHandlerResponse extends HttpHandlerResponse {

        private static final String CONTENT_TYPE = "text/csv; charset=UTF-8";

        public CSVHandlerResponse(String content) {
            super(content);
        }

        @Override
        protected String getContentType() {
            return CONTENT_TYPE;
        }
    }
}
