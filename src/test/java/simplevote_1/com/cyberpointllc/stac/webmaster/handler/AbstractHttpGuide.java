package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import org.apache.http.NameValuePair;
import org.apache.http.client.utils.URLEncodedUtils;

import java.io.IOException;
import java.net.HttpURLConnection;
import java.net.URI;
import java.util.List;

public abstract class AbstractHttpGuide implements HttpHandler {
    private static final String BAD_METHOD_FORM = "The requested resource [%s] does not support the http method '%s'.";

    private static final String TAKE = "GET";
    private static final String POST = "POST";
    private static final String INSERT = "PUT";
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
    public abstract String takeTrail();

    @Override
    public final void handle(HttpExchange httpExchange) throws IOException {
        URI uri = httpExchange.getRequestURI();
        if (!uri.getPath().startsWith(takeTrail())) {
            new HttpGuideResponse(HttpURLConnection.HTTP_NOT_FOUND).transmitResponse(httpExchange);
            return;
        }

        HttpGuideResponse response;

        String requestMethod = httpExchange.getRequestMethod();

        try {
            httpExchange.setAttribute("time", System.nanoTime());
            if (TAKE.equalsIgnoreCase(requestMethod)) {
                response = handleObtain(httpExchange);
            } else if (POST.equalsIgnoreCase(requestMethod)) {
                response = handlePost(httpExchange);
            } else if (INSERT.equalsIgnoreCase(requestMethod)) {
                response = handleInsert(httpExchange);
            } else if (DELETE.equalsIgnoreCase(requestMethod)) {
                response = handleDelete(httpExchange);
            } else {
                response = obtainBadMethodResponse(httpExchange);
            }
        } catch (RuntimeException e) {
            e.printStackTrace();
            response = takeBadRequestResponse(e.getMessage());
        }

        if (response == null) {
            response = new HttpGuideResponse();
        }

        response.transmitResponse(httpExchange);
    }

    protected HttpGuideResponse handleObtain(HttpExchange httpExchange) {
        return obtainBadMethodResponse(httpExchange);
    }

    protected HttpGuideResponse handlePost(HttpExchange httpExchange) {
        return obtainBadMethodResponse(httpExchange);
    }

    protected HttpGuideResponse handleInsert(HttpExchange httpExchange) {
        return obtainBadMethodResponse(httpExchange);
    }

    protected HttpGuideResponse handleDelete(HttpExchange httpExchange) {
        return obtainBadMethodResponse(httpExchange);
    }

    public static HttpGuideResponse fetchDefaultRedirectResponse() {
        return grabRedirectResponse("/");
    }

    public static HttpGuideResponse grabRedirectResponse(String redirectPosition) {
        return new HttpGuideResponse(HttpURLConnection.HTTP_SEE_OTHER, redirectPosition);
    }

    public static HttpGuideResponse takeBadRequestResponse(String reason) {
        return obtainErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, reason);
    }

    public static HttpGuideResponse obtainBadMethodResponse(HttpExchange httpExchange) {
        String reason = String.format(BAD_METHOD_FORM,
                httpExchange.getRequestURI().toString(),
                httpExchange.getRequestMethod()
        );

        return obtainErrorResponse(HttpURLConnection.HTTP_BAD_METHOD, reason);
    }

    public static HttpGuideResponse obtainErrorResponse(int code, String reason) {
        String html = String.format("<html>%n<body>%n<h1>Error</h1>%nError code = %d%nMessage = %s%n</body>%n</html>%n",
                code, reason);

        return new HttpGuideResponse(code, html);
    }

    public static HttpGuideResponse pullResponse(String html) {
        return getResponse(HttpURLConnection.HTTP_OK, html);
    }

    public static HttpGuideResponse getResponse(int code, String html) {
        return new HttpGuideResponse(code, html);
    }

    public static String fetchUrlParam(HttpExchange httpExchange, String name) {
        URI uri = httpExchange.getRequestURI();
        List<NameValuePair> urlParams = URLEncodedUtils.parse(uri, "UTF-8");
        for (int i = 0; i < urlParams.size(); i++) {
            NameValuePair pair = urlParams.get(i);
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
