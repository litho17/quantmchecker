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
        @Inv("+<self>=+c15-c14") StringBuilder builder = new  StringBuilder();
        c14: for (String paragraph : lineBreak.breakParagraphs(content, "<br/>")) {
            c15: formatLongStringHelper(paragraph, builder);
        }
        return builder.toString();
    }

    @Summary({"builder", "1"})
    private static void formatLongStringHelper(String paragraph, @Inv("+<self>=+c23+c24+c25") StringBuilder builder) {
        c23: builder.append("<p>");
        c24: builder.append(paragraph);
        c25: builder.append("</p>");
    }
}
