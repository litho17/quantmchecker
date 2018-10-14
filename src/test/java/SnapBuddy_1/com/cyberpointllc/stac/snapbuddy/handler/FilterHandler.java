package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.net.HttpURLConnection;
import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Filter;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.FilterFactory;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
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

public class FilterHandler extends AbstractTemplateSnapBuddyHandler {

    private final String redirectResponsePath;

    private static final int FILTER_LIMIT = 4;

    private static final Collection<Filter> filters = FilterFactory.getFilters();

    private static final String PATH = "/filter/";

    private static final String TITLE = "Apply Filters";

    private static final String FIELD_NAME = "filter list";

    private static final TemplateEngine IMAGE_TEMPLATE = new  TemplateEngine("    <center>" + "        <div class=\"photos\">" + "            <img src=\" {{photoURL}}\" alt=\"{{photoCaption}}\" /><br/>" + "            {{photoCaption}} " + "        </div>" + "    </center>");

    public FilterHandler(SnapService snapService, String redirectResponsePath) {
        super(snapService);
        this.redirectResponsePath = redirectResponsePath;
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE;
    }

    @Override
    protected String getContents(SnapContext context) {
        String photoPath = context.getPath();
        if (photoPath.startsWith(getPath())) {
            photoPath = photoPath.substring(getPath().length());
        }
        Photo photo = getSnapService().getPhoto(photoPath);
        Person activePerson = context.getActivePerson();
        @Inv("= (- appliedFilters it) (- c64 c63)") List<Filter> appliedFilters = new ArrayList<>();
        @Iter("<= it photo.filters") Iterator<Filter> it = photo.filters.iterator();
        while (it.hasNext()) {
            Filter f;
            c63: f = it.next();
            c64: appliedFilters.add(f);
        }
        String handlerPath = PATH + photoPath;
        @Bound("+ photo.filters 2 FILTER_LIMIT 8") int k;
        @Inv("= (- sb i) (- (+ c81 c83 c71 c72 c73 c76 c77 c87 c88 c89) c85)") StringBuilder sb = new  StringBuilder();
        @Inv("= map (+ c74 c75)") Map<String, String> map = new  HashMap();
        if (activePerson.getPhotos().contains(photoPath)) {
            c71: sb.append("<form action=\"");
            c72: sb.append(handlerPath);
            c73: sb.append("\" method=\"post\" enctype=\"multipart/form-data\">");
            c74: map.put("photoURL", getPhotoUrl(photo));
            c75: map.put("photoCaption", photo.getCaption());
            c76: sb.append(IMAGE_TEMPLATE.replaceTags(map));
            c77: sb.append("<center>");
            // The remaining lists will be initialized with No Filter.
            for (@Iter("<= i FILTER_LIMIT") int i = 0; i < FILTER_LIMIT; ) {
                if (i >= appliedFilters.size()) {
                    c81: sb.append(createDropDownBox(null));
                } else {
                    c83: sb.append(createDropDownBox(appliedFilters.get(i)));
                }
                c85: i = i + 1;
            }
            c87: sb.append("</br>");
            c88: sb.append("<input type=\"submit\" value=\"Apply Filters\" name=\"submit\"></center>");
            c89: sb.append("</form>");
        } else {
            throw new  IllegalArgumentException("This is not your photo.");
        }
        return sb.toString();
    }

    @Override
    public String getPath() {
        return PATH;
    }

    /*
     * Creates a drop-down list of all filters, with the given filter selected.
     * If null is given, "No Filter" is selected
     */
    private String createDropDownBox(Filter appliedFilter) {
        @Bound("+ (* 5 filters) 7") int i;
        @Inv("= (- sb it it it it it) (- (+ c100 c101 c102 c104 c107 c109 c115 c116 c119 c121 c123 c124 c126) c114 c114 c114 c114 c114)") StringBuilder sb = new  StringBuilder();
        c100: sb.append("<select name=\"");
        c101: sb.append(FIELD_NAME);
        c102: sb.append("\">");
        // make an option for No Filter
        c104: sb.append("<option value=\"No Filter\"");
        // decide if this should be the default option
        if (appliedFilter == null) {
            c107: sb.append("selected");
        }
        c109: sb.append(">No Filter</option>");
        // make an option for each filter
        @Iter("<= it filters") Iterator<Filter> it = filters.iterator();
        while (it.hasNext()) {
            Filter filter;
            c114: filter = it.next();
            c115: sb.append("<option value=\"");
            c116: sb.append(filter.getIdentity());
            // decide if this should be the default option
            if (filter.equals(appliedFilter)) {
                c119: sb.append("\" selected>");
            } else {
                c121: sb.append("\">");
            }
            c123: sb.append(filter.getName());
            c124: sb.append("</option>");
        }
        c126: sb.append("</select></br>");
        return sb.toString();
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        SnapService snapService = getSnapService();
        String path = httpExchange.getRequestURI().getPath();
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
        }
        Photo photo = snapService.getPhoto(path);
        // remove all current filters
        for (Filter filter : photo.getFilters()) {
            snapService.removeFilter(photo, filter);
            // update the photo here
            photo = snapService.getPhoto(photo.getIdentity());
        }
        // List<String> filtersToApply = MultipartHelper.getMultipartFieldItems(httpExchange, FIELD_NAME);

        if (httpExchange == null) {
            throw new  IllegalArgumentException("HttpExchange may not be null");
        }
        if (StringUtils.isBlank(FIELD_NAME)) {
            throw new  IllegalArgumentException("Field name may not be blank or null");
        }
        MultipartHelper.HttpExchangeRequestContext context = new MultipartHelper.HttpExchangeRequestContext(httpExchange);
        FileUpload fileUpload = new  FileUpload();
        FileItemFactory fileItemFactory = new DiskFileItemFactory();
        fileUpload.setFileItemFactory(fileItemFactory);
        @Bound("* 3 httpExchange.context.fieldName") int i;
        @Inv("= (- itemStrings it) (- c268 c267)") List<String> itemStrings = new ArrayList();
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


        if (itemStrings.size() > FILTER_LIMIT) {
            return getErrorResponse(HttpURLConnection.HTTP_BAD_METHOD, "You can only specify " + FILTER_LIMIT + " filters");
        }
        @Inv("= (- appliedFilters it1 it2) (- (+ c179 c202) c178 c195)") Set<String> appliedFilters = new  HashSet();
        // apply new filters
        @Iter("<= it1 itemStrings") Iterator<String> it1 = itemStrings.iterator();
        while (it1.hasNext()) {
            String s;
            c178: s = it1.next();
            c179: appliedFilters.add(s);
        }
        @Iter("<= it2 itemStrings") Iterator<String> it2 = itemStrings.iterator();
        while (it2.hasNext()) {
            String filterName;
            c195: filterName = it2.next();
            if (!filterName.equals("No Filter")) {
                Filter filter = FilterFactory.getFilter(filterName);
                if (filter != null) {
                    if (appliedFilters.contains(filterName)) {
                        return getErrorResponse(HttpURLConnection.HTTP_BAD_METHOD, "You cannot apply the same filter " + "more than once");
                    }
                    c202: appliedFilters.add(filterName);
                    snapService.addFilter(photo, filter);
                }
                // update the photo here
                photo = snapService.getPhoto(photo.getIdentity());
            }
        }
        String urlEnd = "";
        String suppressTimestamp = getUrlParam(httpExchange, "suppressTimestamp");
        if (suppressTimestamp != null && suppressTimestamp.equals("true")) {
            urlEnd += "?suppressTimestamp=true";
        }
        return getRedirectResponse(redirectResponsePath + photo.getIdentity() + urlEnd);
    }
}
