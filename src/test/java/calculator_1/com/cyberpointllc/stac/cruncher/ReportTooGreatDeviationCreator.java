package calculator_1.com.cyberpointllc.stac.cruncher;

public class ReportTooGreatDeviationCreator {
    private String message;

    public ReportTooGreatDeviationCreator assignMessage(String message) {
        this.message = message;
        return this;
    }

    public ReportTooGreatDeviation composeReportTooGreatDeviation() {
        return new ReportTooGreatDeviation(message);
    }
}