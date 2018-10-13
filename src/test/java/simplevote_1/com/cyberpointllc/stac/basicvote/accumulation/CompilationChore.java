package simplevote_1.com.cyberpointllc.stac.basicvote.accumulation;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.SurveyOutcomes;
import simplevote_1.com.cyberpointllc.stac.basicvote.DirectVoteService;

import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Aggregates task (optionally, only if time elapsed since last aggregation exceeds updateInterval)
 */
public class CompilationChore implements Runnable {
    private long updateInterval; // perform update if it hasn't been done in this interval (millis)
    private final DirectVoteService voteService;
    private final boolean assessInterval;

    private String fixedSurveyId;

    /**
     * Constructor that updates a single election
     *
     * @param surveyId           election to update (every time this task is run)
     * @param voteService          used to update election results
     * @param updateIntervalMillis interval after which to update results
     * @param assessInterval        if true, checks that updateInterval has elapsed since last update
     */
    public CompilationChore(String surveyId, DirectVoteService voteService, long updateIntervalMillis, boolean assessInterval) {
        this.voteService = voteService;
        this.assessInterval = assessInterval;
        this.updateInterval = updateIntervalMillis;
        this.fixedSurveyId = surveyId;
    }

    /**
     * Constructor that updates all elections
     *
     * @param voteService   used to update election results
     * @param assessInterval if true, checks that updateInterval has elapsed since last update
     */
    public CompilationChore(DirectVoteService voteService, long updateIntervalMillis, boolean assessInterval) {
        this.voteService = voteService;
        this.updateInterval = updateIntervalMillis;
        this.assessInterval = assessInterval;
    }

    public void run() {
        System.out.println("Aggregation task running");
        Set<Survey> surveys;
        if (fixedSurveyId == null) {
            // if no electionId was assigned, collect all elections
            // that have started or started in the past
            Date now = new Date();
            surveys = voteService.pullSurveys().stream()
                    .filter(survey -> !survey.isBeforeSurveyStart(now))
                    .sorted(Comparator.comparing(Survey::obtainSurveyId))
                    .collect(Collectors.toCollection(LinkedHashSet::new));
        } else {
            // if we have a fixed electionId, use only that election
            surveys = Collections.singleton(voteService.fetchSurvey(fixedSurveyId));
        }
        surveys.forEach(this::update); // TODO: do we need to space these out to prevent clumping?
    }

    private void update(Survey survey) {
        if (survey != null && (!assessInterval || isDueForUpdate(survey))) {
            updateAid(survey);
        }
    }

    private void updateAid(Survey survey) {
        try {
            voteService.updateOutcomes(survey);
            System.out.println("Aggregation task updating election " + survey.obtainSurveyId());

            try {
                Thread.sleep(300);
            } catch (InterruptedException e) {
                System.err.println("Pause between updates was interrupted");
            }
        } catch (Exception e) {
            System.err.println("Unable to update election " + survey + ": " + e);
        }
    }

    private boolean isDueForUpdate(Survey survey) {
        SurveyOutcomes outcomes = voteService.fetchAccruedSurveyOutcomes(survey);
        long elapsedTime;
        Date lastUpdate;
        if (outcomes == null) {
            elapsedTime = Long.MAX_VALUE;
            lastUpdate = new Date(Long.MIN_VALUE);
        } else {
            lastUpdate = outcomes.obtainTimestamp();
            elapsedTime = System.currentTimeMillis() - lastUpdate.getTime();
            System.out.println("Elapsed time " + elapsedTime);
        }
        // if the election has completed since the last update, we should update regardless of elapsed time
        if (survey.isAfterSurveyEnd(new Date())) {
            return !survey.isAfterSurveyEnd(lastUpdate);
        } else { // otherwise, look at time elapsed
            return (elapsedTime > updateInterval);
        }
    }
}
