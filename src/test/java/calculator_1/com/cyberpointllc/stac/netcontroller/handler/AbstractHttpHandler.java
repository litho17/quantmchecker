package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import org.apache.http.NameValuePair;
import org.apache.http.client.utils.URLEncodedUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.IOException;
import java.net.HttpURLConnection;
import java.net.URI;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

public abstract class AbstractHttpHandler implements HttpHandler {
    private static final Logger logger = LoggerFactory.getLogger(AbstractHttpHandler.class);

    private static final String BAD_OPERATION_FORMAT = "The requested resource [%s] does not support the http method '%s'.";

    private static final String GRAB = "GET";
    private static final String PARCEL = "POST";
    private static final String PLACE = "PUT";
    private static final String DELETE = "DELETE";

    private final ExecutorService executorService = Executors.newSingleThreadExecutor();

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
    public abstract String grabWalk();

    @Override
    public final void handle(HttpExchange httpExchange) throws IOException {
        // DEBUG: System.out.println("handle: X-tid:" + httpExchange.getRequestHeaders().getFirst("x-tid"));
        Future<Void> future = executorService.submit(() -> {
            doHandle(httpExchange);
            return null;
        });

        try {
            future.get();
        } catch (InterruptedException e) {
            logger.warn("Unexpected interrupt received while processing HttpExchange", e);
        } catch (ExecutionException e) {
            if (e.getCause() instanceof IOException) {
                throw (IOException) e.getCause();
            }

            logger.warn("Unexpected execution error received while processing HttpExchange", e);
        }
    }

    private void doHandle(HttpExchange httpExchange) throws IOException {
        URI uri = httpExchange.getRequestURI();

        if (!uri.getPath().startsWith(grabWalk())) {
            new HttpHandlerResponse(HttpURLConnection.HTTP_NOT_FOUND).sendResponse(httpExchange);
            return;
        }

        HttpHandlerResponse response;

        String solicitationOperation = httpExchange.getRequestMethod();

        try {
            httpExchange.setAttribute("time", System.nanoTime());
            if (GRAB.equalsIgnoreCase(solicitationOperation)) {
                response = handlePull(httpExchange);
            } else if (PARCEL.equalsIgnoreCase(solicitationOperation)) {
                response = handleParcel(httpExchange);
            } else if (PLACE.equalsIgnoreCase(solicitationOperation)) {
                response = handlePlace(httpExchange);
            } else if (DELETE.equalsIgnoreCase(solicitationOperation)) {
                response = handleDelete(httpExchange);
            } else {
                response = getBadOperationResponse(httpExchange);
            }
        } catch (RuntimeException e) {
            e.printStackTrace();
            response = obtainBadSolicitationResponse(e.getMessage());
        }

        if (response == null) {
            response = new HttpHandlerResponse();
        }

        response.sendResponse(httpExchange);
        // DEBUG: System.out.println("doHandle finished: X-tid:" + httpExchange.getRequestHeaders().getFirst("x-tid"));
    }

    protected HttpHandlerResponse handlePull(HttpExchange httpExchange) {
        return getBadOperationResponse(httpExchange);
    }

    protected HttpHandlerResponse handleParcel(HttpExchange httpExchange) {
        return getBadOperationResponse(httpExchange);
    }

    protected HttpHandlerResponse handlePlace(HttpExchange httpExchange) {
        return getBadOperationResponse(httpExchange);
    }

    protected HttpHandlerResponse handleDelete(HttpExchange httpExchange) {
        return getBadOperationResponse(httpExchange);
    }

    public static HttpHandlerResponse obtainDefaultRedirectResponse() {
        return grabRedirectResponse("/");
    }

    public static HttpHandlerResponse grabRedirectResponse(String redirectEnvironment) {
        return new HttpHandlerResponse(HttpURLConnection.HTTP_SEE_OTHER, redirectEnvironment);
    }

    public static HttpHandlerResponse obtainBadSolicitationResponse(String reason) {
        return pullErrorResponse(HttpURLConnection.HTTP_BAD_REQUEST, reason);
    }

    public static HttpHandlerResponse getBadOperationResponse(HttpExchange httpExchange) {
        String reason = String.format(BAD_OPERATION_FORMAT,
                httpExchange.getRequestURI().toString(),
                httpExchange.getRequestMethod()
        );

        return pullErrorResponse(HttpURLConnection.HTTP_BAD_METHOD, reason);
    }

    public static HttpHandlerResponse pullErrorResponse(int code, String reason) {
        String html = String.format("<html>%n<body>%n<h1>Error</h1>%nError code = %d%nMessage = %s%n</body>%n</html>%n",
                code, reason);

        return new HttpHandlerResponse(code, html);
    }

    public static HttpHandlerResponse pullResponse(String html) {
        return fetchResponse(HttpURLConnection.HTTP_OK, html);
    }

    public static HttpHandlerResponse fetchResponse(int code, String html) {
        return new HttpHandlerResponse(code, html);
    }

    public static String grabUrlParam(HttpExchange httpExchange, String name) {
        URI uri = httpExchange.getRequestURI();
        @InvUnk("Unknown API") List<NameValuePair> urlParams = URLEncodedUtils.parse(uri, "UTF-8");
        for (int b = 0; b < urlParams.size(); b++) {
            NameValuePair pair = urlParams.get(b);
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
    public long obtainDuration(HttpExchange httpExchange) {
        long startTime = (long) httpExchange.getAttribute("time");
        return System.nanoTime() - startTime;
    }
}
