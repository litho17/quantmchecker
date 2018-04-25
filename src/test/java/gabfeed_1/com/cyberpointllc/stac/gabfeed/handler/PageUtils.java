package gabfeed_1.com.cyberpointllc.stac.gabfeed.handler;

import gabfeed_1.com.cyberpointllc.stac.linebreak.LineBreak;
import gabfeed_1.com.cyberpointllc.stac.webserver.WebSession;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

public class PageUtils {

    public static String formatLongString(String content, WebSession webSession) {
        String widthString = webSession.getProperty(WidthHandler.PROPERTY_NAME, "80");
        int width = Integer.parseInt(widthString);
        LineBreak lineBreak = new  LineBreak(width);
        String delim = "<br/>";
        @Inv("lineBreak.breakParagraphs(content, delim)+<self>/3=+c16-c15") StringBuilder builder = new  StringBuilder();
        c15: for (String paragraph : lineBreak.breakParagraphs(content, delim)) {
            c16: formatLongStringHelper(paragraph, builder);
        }
        return builder.toString();
    }

    @Summary({"builder", "3"})
    private static void formatLongStringHelper(String paragraph, StringBuilder builder) {
        builder.append("<p>");
        builder.append(paragraph);
        builder.append("</p>");
    }
}
