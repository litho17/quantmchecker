package calculator_1.com.cyberpointllc.stac;

import calculator_1.com.cyberpointllc.stac.netcontroller.handler.LoginHandler;
import com.sun.net.httpserver.HttpExchange;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    public void main(List<HttpExchange> input) {
        @Inv("(and (= (- loginHandler.netSessionService.sessions it) (- c20 c19)) (= (- loginHandler.netSessionService.times it) (- c20 c19)))") LoginHandler loginHandler = null;
        HttpExchange h;
        Iterator<HttpExchange> it = input.iterator();
        while (it.hasNext()) {
            c19: h = it.next();
            c20: loginHandler.handleParcel(h);
        }
    }
}
