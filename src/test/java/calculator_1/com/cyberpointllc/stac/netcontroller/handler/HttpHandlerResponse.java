package calculator_1.com.cyberpointllc.stac.netcontroller.handler;

import com.sun.net.httpserver.HttpExchange;

import java.io.IOException;
import java.io.InputStream;
import java.net.HttpURLConnection;

public class HttpHandlerResponse {
    private static final String CONTENT_TYPE = "text/html; charset=UTF-8";
    private static final int DEFAULT_BUFFER_CONTENT = 4096;

    private final int code;
    private final String response;

    public HttpHandlerResponse() {
        this(HttpURLConnection.HTTP_OK);
    }

    public HttpHandlerResponse(int code) {
        this(code, "");
    }

    public HttpHandlerResponse(String response) {
        this(HttpURLConnection.HTTP_OK, response);
    }

    public HttpHandlerResponse(int code, String response) {
        this.code = code;
        this.response = (response == null) ? "" : response;
    }

    protected String fetchContentType() {
        return CONTENT_TYPE;
    }

    protected void integrateResponseHeaders(HttpExchange httpExchange) throws IOException {
        // Forces caches to obtain a new copy of the page from the server
        httpExchange.getResponseHeaders().set("Cache-Control", "no-cache");

        // Directs caches not to store the page under any circumstance
        httpExchange.getResponseHeaders().add("Cache-Control", "no-store");

        // Causes the proxy cache to see the page as "stale"
        httpExchange.getResponseHeaders().set("Expires", "0");

        // HTTP 1.0 backward compatibility for caching
        httpExchange.getResponseHeaders().set("Pragma", "no-cache");

        // Make sure Content-Type is properly set
        httpExchange.getResponseHeaders().set("Content-Type", fetchContentType());

        // Low volume requests, so close after each connection
        httpExchange.getResponseHeaders().set("Connection", "close");
    }

    protected byte[] getResponseBytes(HttpExchange httpExchange) throws IOException {
        String response = (this.response == null) ? "" : this.response;

        // Special handling of redirects
        if ((HttpURLConnection.HTTP_SEE_OTHER == code || HttpURLConnection.HTTP_MOVED_PERM == code ) && !response.isEmpty()) {
            httpExchange.getResponseHeaders().set("Location", response.trim());
            response = "";
        }

        return response.getBytes("UTF-8");
    }

    public void sendResponse(HttpExchange httpExchange) throws IOException {
        integrateResponseHeaders(httpExchange);

        byte[] bytes = getResponseBytes(httpExchange);

        if (bytes == null) {
            bytes = new byte[0];
        }

        httpExchange.sendResponseHeaders(code, bytes.length);

        httpExchange.getResponseBody().write(bytes);
        drain(httpExchange.getRequestBody());
        httpExchange.close();
    }

    /**
     * Reads and discards any remaining bytes in the input stream.
     * Closing an HttpExchange without consuming all of the request
     * body (InputStream) is not an error but may make the underlying
     * TCP connection unusable for following exchanges.
     * The default InputStream assigned by the HttpExchange will be
     * a subclass of sun.net.httpserver.LeftOverInputStream which,
     * on a call to close, will attempt to drain the InputStream.
     * However, that implementation will only drain up to a fixed size
     * (see ServerConfig.getDrainAmount - default: 64 x 1024 bytes).
     * This method completely drains the stream so, when close
     * is called, the stream has been completely read.
     */
    private void drain(InputStream inputStream) throws IOException {
        byte[] buffer = new byte[DEFAULT_BUFFER_CONTENT];
        int count;
        do {
            count = inputStream.read(buffer);
        } while (count != -1);
    }
}
