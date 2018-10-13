package airplan_1.edu.cyberapex.record.helpers;

import airplan_1.edu.cyberapex.record.event.SubstituteLoggingEvent;

import java.util.List;

public class SubstituteLoggerBuilder {
    private String name;
    private List<SubstituteLoggingEvent> eventList;

    public SubstituteLoggerBuilder defineName(String name) {
        this.name = name;
        return this;
    }

    public SubstituteLoggerBuilder defineEventList(List<SubstituteLoggingEvent> eventList) {
        this.eventList = eventList;
        return this;
    }

    public SubstituteLogger generateSubstituteLogger() {
        return new SubstituteLogger(name, eventList);
    }
}