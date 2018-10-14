package SnapBuddy_1.com.cyberpointllc.stac.webserver.handler;

import SnapBuddy_1.com.cyberpointllc.stac.webserver.User;
import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import org.apache.http.NameValuePair;
import org.apache.http.client.utils.URLEncodedUtils;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.IOException;
import java.net.HttpURLConnection;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

public abstract class AbstractHttpHandler implements HttpHandler {

    private static final String BAD_METHOD_FORMAT = "The requested resource [%s] does not support the http method '%s'.";

    private static final String GET = "GET";

    private static final String POST = "POST";

    private static final String PUT = "PUT";

    private static final String DELETE = "DELETE";

    /**
     * Returns the path associated with this handler.
     * This <em>must</em> not be <code>null</code> and
     * <em>must</em> begin with a slash (<code>/</code>) character.
     * This may just represent the start of a REST path
     * with the remainder representing the argument.
     *
     * @return String representing the path to this handler;
     * guaranteed to not be <code>null</code>
     */
    public abstract String getPath();

    @Override
    public final void handle(HttpExchange httpExchange) throws IOException {
        if (!httpExchange.getRequestURI().getPath().startsWith(getPath())) {
            httpExchange.sendResponseHeaders(HttpURLConnection.HTTP_NOT_FOUND, 0);
            httpExchange.close();
            return;
        }
        HttpHandlerResponse response;
        String requestMethod = httpExchange.getRequestMethod();
        try {
            httpExchange.setAttribute("time", System.nanoTime());
            if (GET.equalsIgnoreCase(requestMethod)) {
                response = handleGet(httpExchange);
            } else if (POST.equalsIgnoreCase(requestMethod)) {
                response = handlePost(httpExchange);
            } else if (PUT.equalsIgnoreCase(requestMethod)) {
                response = handlePut(httpExchange);
            } else if (DELETE.equalsIgnoreCase(requestMethod)) {
                response = handleDelete(httpExchange);
            } else {
                response = getBadMethodResponse(httpExchange);
            }
        } catch (RuntimeException e) {
            e.printStackTrace();
            response = getErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, e.getMessage());
        }
        if (response == null) {
            response = new  HttpHandlerResponse();
        }
        response.sendResponse(httpExchange);
    }

    protected HttpHandlerResponse handleGet(HttpExchange httpExchange) {
        return getBadMethodResponse(httpExchange);
    }

    protected HttpHandlerResponse handlePost(HttpExchange httpExchange) {
        return getBadMethodResponse(httpExchange);
    }

    protected HttpHandlerResponse handlePut(HttpExchange httpExchange) {
        return getBadMethodResponse(httpExchange);
    }

    protected HttpHandlerResponse handleDelete(HttpExchange httpExchange) {
        return getBadMethodResponse(httpExchange);
    }

    public static HttpHandlerResponse getDefaultRedirectResponse() {
        return getRedirectResponse("/");
    }

    public static HttpHandlerResponse getRedirectResponse(String redirectLocation) {
        return new  HttpHandlerResponse(HttpURLConnection.HTTP_SEE_OTHER, redirectLocation);
    }

    public static HttpHandlerResponse getBadMethodResponse(HttpExchange httpExchange) {
        String reason = String.format(BAD_METHOD_FORMAT, httpExchange.getRequestURI().toString(), httpExchange.getRequestMethod());
        return getErrorResponse(HttpURLConnection.HTTP_BAD_METHOD, reason);
    }

    public static HttpHandlerResponse getErrorResponse(int code, String reason) {
        String html = String.format("<html>%n<body>%n<h1>Error</h1>%nError code = %d%nMessage = %s%n</body>%n</html>%n", code, reason);
        return new  HttpHandlerResponse(code, html);
    }

    public static HttpHandlerResponse getResponse(String html) {
        return getResponse(HttpURLConnection.HTTP_OK, html);
    }

    public static HttpHandlerResponse getResponse(int code, String html) {
        return new  HttpHandlerResponse(code, html);
    }

    public static String getUrlParam(HttpExchange httpExchange, String name) {
        URI uri = httpExchange.getRequestURI();
        @Bound("uri") int i;
        @InvUnk("Unknown API") List<NameValuePair> pairs = URLEncodedUtils.parse(uri, "UTF-8");
        @Inv("= (- urlParams it) (- c128 c127)") List<NameValuePair> urlParams = new ArrayList<>();
        @Iter("<= it uri") Iterator<NameValuePair> it = pairs.iterator();
        while (it.hasNext()) {
            NameValuePair n;
            c127: n = it.next();
            c128: urlParams.add(n);
        }
        for (NameValuePair pair : urlParams) {
            if (pair.getName().equals(name)) {
                return pair.getValue();
            }
        }
        return null;
    }

    /**
     * Returns the difference between the current time and the last time handle was
     * called.
     */
    public long getDuration(HttpExchange httpExchange) {
        long startTime = (long) httpExchange.getAttribute("time");
        return System.nanoTime() - startTime;
    }
}
