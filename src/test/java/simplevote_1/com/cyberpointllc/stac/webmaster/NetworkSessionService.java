package simplevote_1.com.cyberpointllc.stac.webmaster;

import com.sun.net.httpserver.HttpExchange;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.TimeUnit;

public class NetworkSessionService {
    private static final String COOKIE_EXPIRATION = "86400";
    private final Map<String, Long> times = new HashMap<>();
    private final Map<String, NetworkSession> sessions = new HashMap<>();
    private final long sessionExpirationInNanos;
    private final String cookieName;

    public NetworkSessionService(String applicationBaseName, long sessionExpirationInMinutes) {
        this.cookieName = applicationBaseName + "_sessionId";
        this.sessionExpirationInNanos = TimeUnit.NANOSECONDS.convert(sessionExpirationInMinutes, TimeUnit.MINUTES);
    }

    /**
     * Adds a session to the map of managed sessions. Adds a cookie to the
     * HttpExchange that allows the user to continue to access the same session.
     * @param httpExchange
     * @param session containing the userId of the current user
     */
    public void addSession(HttpExchange httpExchange, NetworkSession session) {
        // create session id
        String sessionId = UUID.randomUUID().toString();
        sessions.put(sessionId, session);
        times.put(sessionId, System.nanoTime());

        // add cookies
        assignCookie(httpExchange, sessionId, COOKIE_EXPIRATION);

    }

    /**
     * Retrieves the session given the HttpExchange. The HttpExchange must contain
     * a cookie that specifies the sessionId. If no cookie exists, this returns null.
     * @param httpExchange
     * @return WebSession specifying the user id of the current user; may be null
     * if the sessionId cannot be found or if the WebSession has expired.
     */
    public NetworkSession takeSession(HttpExchange httpExchange) {
        String sessionId = getSessionIdFromCookie(httpExchange);
        if (sessionId != null && sessions.containsKey(sessionId)) {
            // check if the session is still valid
            if ((System.nanoTime() - times.get(sessionId)) > sessionExpirationInNanos) {
                return new NetworkSessionServiceCoordinator(httpExchange).invoke();
            } else {
                // update the last time the session was used
                return new NetworkSessionServiceSupervisor(httpExchange, sessionId).invoke();

            }
        }
        return null;
    }

    /**
     * Parses the cookies found in the HttpExchange to find the sessionId if one exists.
     * If no sessionId exists, this returns null;
     */
    private String getSessionIdFromCookie(HttpExchange httpExchange) {
        List<String> cookies = httpExchange.getRequestHeaders().get("Cookie");
        if (cookies != null) {
            for (int i1 = 0; i1 < cookies.size(); i1++) {
                String cookie = cookies.get(i1);
                String[] cookiePieces = cookie.split(";");
                for (int c = 0; c < cookiePieces.length; c++) {
                    String cookiePiece = cookiePieces[c];
                    String[] cookieNameEssencePair = cookiePiece.split("=");
                    if (cookieName.equals(cookieNameEssencePair[0].trim())) {
                        return cookieNameEssencePair[1].trim();
                    }
                }
            }
        }
        return null;
    }

    private void assignCookie(HttpExchange httpExchange, String sessionId, String maxAge) {
        httpExchange.getResponseHeaders().set("Set-Cookie", cookieName + "=" + sessionId + "; path=/; HttpOnly " +
                "; max-age="+ maxAge + "; Secure; ");
    }

    public void invalidateSession(HttpExchange httpExchange) {
        String sessionId = getSessionIdFromCookie(httpExchange);
        if (sessionId != null) {
            invalidateSessionCoordinator(httpExchange, sessionId);
        }
    }

    private void invalidateSessionCoordinator(HttpExchange httpExchange, String sessionId) {
        sessions.remove(sessionId);
        times.remove(sessionId);

        //set the cookie's max-age to 0
        assignCookie(httpExchange, sessionId, "0");
    }

    private class NetworkSessionServiceCoordinator {
        private HttpExchange httpExchange;

        public NetworkSessionServiceCoordinator(HttpExchange httpExchange) {
            this.httpExchange = httpExchange;
        }

        public NetworkSession invoke() {
            invalidateSession(httpExchange);
            return null;
        }
    }

    private class NetworkSessionServiceSupervisor {
        private HttpExchange httpExchange;
        private String sessionId;

        public NetworkSessionServiceSupervisor(HttpExchange httpExchange, String sessionId) {
            this.httpExchange = httpExchange;
            this.sessionId = sessionId;
        }

        public NetworkSession invoke() {
            times.put(sessionId, System.nanoTime());
            // set the cookie again
            assignCookie(httpExchange, sessionId, COOKIE_EXPIRATION);
            return sessions.get(sessionId);
        }
    }
}
