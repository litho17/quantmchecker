package SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler;

import java.util.Map;
import java.util.HashMap;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapContext;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.SnapService;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Person;
import SnapBuddy_1.com.cyberpointllc.stac.snapservice.model.Photo;
import SnapBuddy_1.com.cyberpointllc.stac.template.TemplateEngine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

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
        @Bound("11") int i;
        @Inv("= imageMap (+ c44 c45)") Map<String, String> imageMap = new  HashMap();
        @Inv("= sb (+ c46 c47 c48 c49 c53 c56 c57 c59)") StringBuilder sb = new  StringBuilder();
        if (activePerson.getPhotos().contains(path)) {
            c44: imageMap.put("photoPath", getPhotoUrl(photo));
            c45: imageMap.put("currentCaption", photo.getCaption());
            c46: sb.append(IMAGE_TEMPLATE.replaceTags(imageMap));
            c47: sb.append("<center><form action=\"");
            c48: sb.append(PATH);
            c49: sb.append("\" method=\"post\" encytype=\"multipart/form-data\">");
            @Inv("= buttonMap c51") Map<String, String> buttonMap = new  HashMap();
            c51: buttonMap.put("pid", photo.getIdentity());
            // add the filter button
            c53: sb.append(FILTER_TEMPLATE.replaceTags(buttonMap));
            // so it doesn't get these buttons.
            if (!photo.getIdentity().equals(getProfilePhotoIdentity(person))) {
                c56: sb.append(PUBLIC_TEMPLATE.replaceTags(buttonMap));
                c57: sb.append(CAPTION_TEMPLATE.replaceTags(buttonMap));
            }
            c59: sb.append("</form></center>");
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
