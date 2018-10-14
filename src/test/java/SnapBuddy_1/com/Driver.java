package SnapBuddy_1.com;

import SnapBuddy_1.com.cyberpointllc.stac.snapbuddy.handler.*;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSession;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.WebSessionService;
import SnapBuddy_1.com.cyberpointllc.stac.webserver.handler.NoLoginFilter;
import com.sun.net.httpserver.Filter;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    HttpExchange httpExchange;
    Filter.Chain chain;

    NoLoginFilter noLoginFilter;
    CaptionHandler captionHandler;
    FilterHandler filterHandler;
    PublicHandler publicHandler;
    FriendsPhotosHandler friendsPhotosHandler;
    NeighborsHandler neighborsHandler;
    public void main(List<Object> input) throws Exception {
        @Bound("* 2 input") int i;
        @Inv("and (= (- webSessionService.sessions it) (- c33 c32)) (= (- webSessionService.times it) (- c33 c32))") WebSessionService webSessionService = null;
        @Iter("<= it input") Iterator<Object> it = input.iterator();
        while (it.hasNext()) {
            Object o;
            c32: o = it.next();
            c33: noLoginFilter.doFilter(httpExchange, chain);
            captionHandler.handlePost(httpExchange);
            filterHandler.handlePost(httpExchange);
            publicHandler.handlePost(httpExchange);
            neighborsHandler.handle(httpExchange);
        }
    }
}
