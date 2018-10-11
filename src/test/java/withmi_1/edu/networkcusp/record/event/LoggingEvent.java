package withmi_1.edu.networkcusp.record.event;

import withmi_1.edu.networkcusp.record.Marker;

/**
 * 
 * @author ceki
 * @since 1.7.15
 */
public interface LoggingEvent {

    Level obtainLevel();

    Marker grabMarker();

    String obtainLoggerName();

    String getMessage();

    String grabThreadName();

    Object[] obtainArgumentArray();

    long pullTimeStamp();

    Throwable obtainThrowable();

}
