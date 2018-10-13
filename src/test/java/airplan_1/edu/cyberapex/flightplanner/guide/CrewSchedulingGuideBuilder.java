package airplan_1.edu.cyberapex.flightplanner.guide;

import airplan_1.edu.cyberapex.flightplanner.store.AirDatabase;
import airplan_1.edu.cyberapex.server.WebSessionService;

public class CrewSchedulingGuideBuilder {
    private AirDatabase airDatabase;
    private WebSessionService sessionService;

    public CrewSchedulingGuideBuilder fixAirDatabase(AirDatabase airDatabase) {
        this.airDatabase = airDatabase;
        return this;
    }

    public CrewSchedulingGuideBuilder defineSessionService(WebSessionService sessionService) {
        this.sessionService = sessionService;
        return this;
    }

    public CrewSchedulingGuide generateCrewSchedulingGuide() {
        return new CrewSchedulingGuide(airDatabase, sessionService);
    }
}