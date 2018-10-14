package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.*;

import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.HttpHandlerResponse;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.MultipartHelper;
import org.apache.commons.fileupload.FileItem;
import org.apache.commons.fileupload.FileItemFactory;
import org.apache.commons.fileupload.FileUpload;
import org.apache.commons.fileupload.disk.DiskFileItemFactory;
import org.apache.commons.lang3.StringUtils;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

public class NameHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/profilename";

    private static final String TITLE = "Change Name";

    private static final String FIELD_NAME = "changename";

    private static final TemplateEngine TEMPLATE = new  TemplateEngine("<form action\"" + PATH + "\" method=\"post\" enctype=\"multipart/form-data\">" + "    Updated Name: <input type=\"text\" name=\"" + FIELD_NAME + "\" placeholder=\"{{name}}\" /></br> " + "    <input type=\"submit\" value=\"Change Name\" name=\"submit\">" + "</form>");

    public NameHandler(SnapService snapService) {
        super(snapService);
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE;
    }

    @Override
    protected String getContents(SnapContext context) {
        assert (context != null) : "Context may not be null";
        Person person = context.getActivePerson();
        @Bound("1") int i;
        @Inv("= map c45") Map<String, String> map = new HashMap<>();
        c45: map.put("name", person.getName());
        return TEMPLATE.replaceTags(map);
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        Person person = getPerson(httpExchange);
        // List<String> names = MultipartHelper.getMultipartFieldItems(httpExchange, FIELD_NAME);

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
        @Bound("httpExchange.context.fieldName") int i;
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

        String name = "";
        int conditionObj0 = 1;
        // if there is more than one element, the name does not get changed
        if (itemStrings.size() == conditionObj0) {
            name = itemStrings.get(0);
        }
        if (!StringUtils.isBlank(name)) {
            handlePostHelper(person, name);
        }
        return getDefaultRedirectResponse();
    }

    private void handlePostHelper(Person person, String name) {
        getSnapService().setName(person, name);
    }
}
