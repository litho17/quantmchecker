package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.LocationService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.net.HttpURLConnection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Handler that is responsible for both processing a GET request to
 * generate a template-based view to enable the user to submit a file
 * of BSSID values to set their location but also for processing the
 * POST submission to read the file and update the Person's location.
 * The GET request is managed through the parent class abstract methods
 * and the POST is handled by the <code>handlePost</code> method.
 */
public class LocationHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/location";

    private static final String TITLE = "Change Current Location";

    private static final String FIELD_NAME = "bssids";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">" + "    <label for=\"text\">Comma separated list of BSSIDs:</label>" + "    <input type=\"text\" id=\"text\" name=\"" + FIELD_NAME + "\" autofocus required placeholder=\"Enter comma separated list of BSSIDs with no spaces\"/>" + "    <br/>" + "    <input type=\"submit\" value=\"Set Location\" name=\"submit\" id=\"submit\" />" + "</form>");

    private final LocationService locationService;

    public LocationHandler(SnapService snapService, LocationService locationService) {
        super(snapService);
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
    protected String getTitle(SnapContext context) {
        return TITLE;
    }

    @Override
    protected String getContents(SnapContext context) {
        return TEMPLATE.replaceTags(Collections.singletonMap("path", getPath()));
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person person = getPerson(httpExchange);
        String content = MultipartHelper.getMultipartFieldContent(httpExchange, FIELD_NAME);
        // Set<String> accessPoints = parseAccessPoints(content);

        if (StringUtils.isBlank(content)) {
            throw new  IllegalArgumentException("Location setting requires list of BSSIDs");
        }
        String[] parts = content.split("\\s*[\\s,]\\s*");
        @Bound("content") int k;
        @Inv("= (- bssids i) (- c76 c77)") Set<String> bssids = new  HashSet();
        for (@Iter("<= i content") int i = 0; i < parts.length;) {
            c76: bssids.add(parts[i]);
            c77: i = i + 1;
        }

        Location location = locationService.getLocation(bssids);
        if (location == null) {
            throw new  IllegalArgumentException("File of Access Points is either malformed or else does not match a valid location");
        }
        if (getSnapService().canUpdateLocation(person)) {
            getSnapService().setLocation(person, location);
        } else {
            if (!person.getLocation().equals(location)) {
                return getErrorResponse(HttpURLConnection.HTTP_FORBIDDEN, "Number of Location change requests exceeds daily quota");
            }
        }
        return getDefaultRedirectResponse();
    }
}
