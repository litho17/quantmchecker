package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.Map;
import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;

public class EditPhotoHandler extends AbstractTemplateSnapBuddyHandler {

    private static final String PATH = "/editphoto/";

    private static final String TITLE = "Edit Photo";

    private static final TemplateEngine CAPTION_TEMPLATE = new  TemplateEngine("<a href=\"/editcaption/{{pid}}\">" + "    <input type=\"button\" value=\"Change Caption\" name=\"submit\">" + "</a>");

    private static final TemplateEngine PUBLIC_TEMPLATE = new  TemplateEngine("<a href=\"/public/{{pid}}\">" + "    <input type=\"button\" value=\"Change Privacy\" name=\"submit\">" + "</a>");

    private static final TemplateEngine FILTER_TEMPLATE = new  TemplateEngine("<a href=\"/filter/{{pid}}\">" + "    <input type=\"button\" value=\"Add Filters\" name=\"submit\">" + "</a>");

    private static final TemplateEngine IMAGE_TEMPLATE = new  TemplateEngine("<center>" + "    <div class=\"photos\"> " + "        <img src=\"{{photoPath}}\" alt=\"{{currentCaption}}\" /><br/>" + "        {{currentCaption}}" + "    </div>" + "</center>");

    public EditPhotoHandler(SnapService snapService) {
        super(snapService);
    }

    @Override
    protected String getContents(SnapContext context) {
        Person person = context.getActivePerson();
        String path = context.getPath();
        if (path.startsWith(getPath())) {
            path = path.substring(getPath().length());
        }
        Photo photo = getSnapService().getPhoto(path);
        Person activePerson = context.getActivePerson();
        Map<String, String> imageMap = new  HashMap();
        StringBuilder sb = new  StringBuilder();
        if (activePerson.getPhotos().contains(path)) {
            imageMap.put("photoPath", getPhotoUrl(photo));
            imageMap.put("currentCaption", photo.getCaption());
            sb.append(IMAGE_TEMPLATE.replaceTags(imageMap));
            sb.append("<center><form action=\"");
            sb.append(PATH);
            sb.append("\" method=\"post\" encytype=\"multipart/form-data\">");
            Map<String, String> buttonMap = new  HashMap();
            buttonMap.put("pid", photo.getIdentity());
            // add the filter button
            sb.append(FILTER_TEMPLATE.replaceTags(buttonMap));
            // so it doesn't get these buttons.
            if (!photo.getIdentity().equals(getProfilePhotoIdentity(person))) {
                sb.append(PUBLIC_TEMPLATE.replaceTags(buttonMap));
                sb.append(CAPTION_TEMPLATE.replaceTags(buttonMap));
            }
            sb.append("</form></center>");
        } else {
            throw new  IllegalArgumentException("This is not your photo.");
        }
        return sb.toString();
    }

    @Override
    public String getPath() {
        return PATH;
    }

    @Override
    protected String getTitle(SnapContext context) {
        return TITLE;
    }
}
