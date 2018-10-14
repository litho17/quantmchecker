package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.LocationService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Location;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import com.sun.net.httpserver.HttpExchange;
import org.apache.commons.fileupload.FileItem;
import org.apache.commons.fileupload.FileItemFactory;
import org.apache.commons.fileupload.FileUpload;
import org.apache.commons.fileupload.disk.DiskFileItemFactory;
import org.apache.commons.lang3.StringUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.net.HttpURLConnection;

/**
 * Handler that processes a GET request to generate a template-based
 * view to confirm the setting of the Person's current location.
 */
public class LocationConfirmHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/location/confirm";

    private static final String TITLE = "Confirm Initial Location";

    private static final String TEMPLATE_RESOURCE = "basictemplate.html";

    private static final String FIELD_NAME = "identity";

    private static final TemplateEngine CONFIRM_TEMPLATE = new  TemplateEngine("<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">" + "    Your current location will be set to \"{{city}}\".<br/>" + "    <input type=\"hidden\" name=\"{{identity}}\" value=\"{{lid}}\">" + "    <input type=\"submit\" value=\"Confirm Location Setting\">" + "</form>");

    private static final TemplateEngine FIXED_TEMPLATE = new  TemplateEngine("<form action=\"{{path}}\" method=\"post\" enctype=\"multipart/form-data\">" + "    Your current location cannot be modified to \"{{city}}\" because that" + "    change would exceed your daily location change request quota." + "    Your previous location \"{{oldCity}}\" will be maintained.<br/>" + "    <input type=\"hidden\" name=\"{{identity}}\" value=\"{{lid}}\">" + "    <input type=\"submit\" value=\"Continue\">" + "</form>");

    private final LocationService locationService;

    public LocationConfirmHandler(SnapService snapService, LocationService locationService) {
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
    protected String getTemplateResource() {
        return TEMPLATE_RESOURCE;
    }

    @Override
    protected String getContents(SnapContext context) {
        Person person = context.getActivePerson();
        Location previousLocation = person.getLocation();
        String identity = context.getUrlParam("lid");
        if (StringUtils.isBlank(identity)) {
            identity = previousLocation.getIdentity();
        }
        Location location = locationService.getLocation(identity);
        if (location == null) {
            throw new  IllegalArgumentException("Location does not exist for identity " + identity);
        }
        TemplateEngine templateEngine;
        if (location.equals(person.getLocation()) || getSnapService().canUpdateLocation(person)) {
            templateEngine = CONFIRM_TEMPLATE;
        } else {
            templateEngine = FIXED_TEMPLATE;
            identity = previousLocation.getIdentity();
        }
        @Bound("5") int i;
        @Inv("= map (+ c85 c86 c87 c88 c89)") Map<String, String> map = new  HashMap();
        c85: map.put("identity", FIELD_NAME);
        c86: map.put("path", getPath());
        c87: map.put("lid", identity);
        c88: map.put("city", location.getCity());
        c89: map.put("oldCity", previousLocation.getCity());
        return templateEngine.replaceTags(map);
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person person = getPerson(httpExchange);
        // List<String> itemStrings = MultipartHelper.getMultipartFieldItems(httpExchange, FIELD_NAME);

        if (httpExchange == null) {
            throw new  IllegalArgumentException("HttpExchange may not be null");
        }
        if (StringUtils.isBlank(FIELD_NAME)) {
            throw new  IllegalArgumentException("Field name may not be blank or null");
        }
        MultipartHelper.HttpExchangeRequestContext context = new MultipartHelper.HttpExchangeRequestContext(httpExchange);
        FileUpload fileUpload = new  FileUpload();
        FileItemFactory fileItemFactory = new  DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);
        @Bound("httpExchange.context.fieldName") int i;
        @Inv("= (- itemStrings it) (- c268 c267)") List<String> itemStrings = new  ArrayList();
        try {
            // get items associated with the field name
            if (fileUpload.parseParameterMap(context).get(FIELD_NAME) != null && !fileUpload.parseParameterMap(context).get(FIELD_NAME).isEmpty()) {
                @Iter("<= it httpExchange.context.fieldName") Iterator<FileItem> it = fileUpload.parseParameterMap(context).get(FIELD_NAME).iterator();
                while (it.hasNext()) {
                    FileItem item;
                    c267: item = it.next();
                    c268: itemStrings.add(item.getString());
                }
            }
        } catch (Exception e) {
            throw new  IllegalArgumentException("Error parsing multipart message: " + e.getMessage(), e);
        }

        int conditionObj0 = 1;
        if ((itemStrings == null) || (itemStrings.size() != conditionObj0)) {
            // Missing POST field - treat this as "don't change user's location"
            return getDefaultRedirectResponse();
        }
        String identity = itemStrings.get(0);
        if (StringUtils.isBlank(identity)) {
            // Empty POST value - treat this as "don't change user's location"
            return getDefaultRedirectResponse();
        }
        Location location = locationService.getLocation(identity);
        if (location == null) {
            throw new  IllegalArgumentException("Location does not exist for identity " + identity);
        }
        if (location.equals(person.getLocation()) || getSnapService().canUpdateLocation(person)) {
            handlePostHelper(person, location);
        } else {
            return getErrorResponse(HttpURLConnection.HTTP_FORBIDDEN, "Number of Location change requests exceeds daily quota");
        }
        return getDefaultRedirectResponse();
    }

    private void handlePostHelper(Person person, Location location) {
        getSnapService().setLocation(person, location);
    }
}
