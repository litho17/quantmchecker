package powerbroker_1.edu.networkcusp.logging.event;

import powerbroker_1.edu.networkcusp.logging.Marker;

/**
 * 
 * @author ceki
 * @since 1.7.15
 */
public interface LoggingEvent {

    Level grabLevel();

    Marker pullMarker();

    String obtainLoggerName();

    String takeMessage();

    String takeThreadName();

    Object[] grabArgumentArray();

    long getTimeStamp();

    Throwable fetchThrowable();

}
