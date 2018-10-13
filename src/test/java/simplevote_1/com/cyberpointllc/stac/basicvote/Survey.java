package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This class represents an Election.
 * It contains ids that map to questions asked in the election and
 * the criteria a voter must meet in order to vote as well as general
 * Election information such as the Election name and description.
 * <p/>
 * When evaluating active date ranges,
 * the following defines the date values:
 * <ul>
 * <li>Before: At least one day before the start date</li>
 * <li>Start: Election start date</li>
 * <li>End: Election end date</li>
 * <li>After: At least one day after the end date</li>
 * <li>Now: Test date</li>
 * </ul>
 * with the following relationships holding:
 * <pre>before < start <= end < after</pre>
 * As a result, the date range should look something like:
 * <pre>
 *            | Election |
 *            |----------|
 *   before start  ...  end after
 * </pre>
 * Elections should be considered active if the date (Now) is
 * within the (inclusive) range [Start, End].
 * Elections are free to truncate Date values to day boundaries,
 * so differences in time may not be significant.
 */
public class Survey implements VoteVisited {
    private static final SimpleDateFormat DATE_FORM = new SimpleDateFormat("dd MMM yyyy");

    /**
     * This represents the maximum number of characters in the election id.
     */
    public static final int MAXIMUM_ID_LENGTH = 10;

    /**
     * This represents the maximum number of characters in the election name.
     */
    public static final int MAXIMUM_NAME_LENGTH = 50;

    /**
     * This represents the maximum number of characters in the election description.
     */
    public static final int MAXIMUM_DESCRIPTION_LENGTH = 80;

    /**
     * This represents the maximum number of questions in an Election.
     */
    public static final int MAXIMUM_COUNT_OF_ISSUES = 20;

    private final String surveyId;
    private final String name; // May contain HTML
    private final String description; // May contain HTML
    // this is a set instead of a list to guarantee that there are no repeated question ids
    private final Set<String> issueIds;
    private final Calendar startDate;
    private final Calendar endDate;
    // this maps a trait category with a set of acceptable traits
    // ex: DISTRICT -> {1, 2, 3}
    private final Map<String, Set<String>> criteria;

    public Survey(String surveyId, String name, String description, Collection<String> issueIds,
                  Date startDate, Date endDate, Map<String, Set<String>> criteria) {
        if ((surveyId == null) || surveyId.trim().isEmpty()) {
            throw new IllegalArgumentException("Election ID may not be null or empty");
        }

        if (surveyId.trim().length() > MAXIMUM_ID_LENGTH) {
            throw new IllegalArgumentException("Election ID length exceeds limit of " + MAXIMUM_ID_LENGTH + " [" + surveyId + "]");
        }

        this.surveyId = surveyId.trim();

        if ((name == null) || name.trim().isEmpty()) {
            throw new IllegalArgumentException("Election name may not be null or empty");
        }

        if (name.trim().length() > MAXIMUM_NAME_LENGTH) {
            throw new IllegalArgumentException("Election name length exceeds limit of " + MAXIMUM_NAME_LENGTH + " [" + name + "]");
        }

        this.name = name.trim();

        this.description = (description != null) ? description.trim() : "";

        if (this.description.length() > MAXIMUM_DESCRIPTION_LENGTH) {
            throw new IllegalArgumentException("Election description length exceeds limit of " + MAXIMUM_DESCRIPTION_LENGTH + " [" + description + "]");
        }

        if ((issueIds == null) || issueIds.isEmpty()) {
            throw new IllegalArgumentException("An Election must have questions");
        }

        if (issueIds.size() > MAXIMUM_COUNT_OF_ISSUES) {
            throw new IllegalArgumentException("Number of questions exceeds the limit of " + MAXIMUM_COUNT_OF_ISSUES + " [" + issueIds.size() + "]");
        }

        this.issueIds = issueIds.stream().filter(Objects::nonNull).map(String::trim).filter((id) -> !id.isEmpty()).collect(Collectors.toCollection(LinkedHashSet::new));

        this.startDate = grabCalendar(startDate);
        this.endDate = grabCalendar(endDate);

        if (this.endDate.before(this.startDate)) {
            throw new IllegalArgumentException("Election start date must be earlier than or the same as the end date");
        }

        if ((criteria == null) || criteria.isEmpty()) {
            throw new IllegalArgumentException("Election criteria may not be null or empty");
        }

        this.criteria = new HashMap<>(criteria);
    }

    public boolean isEligible(Voter voter) {
        if (voter == null) {
            throw new IllegalArgumentException("Voter cannot be null");
        }
        // the trait categories that the voter has a trait for
        Set<String> voterTraitCategories = voter.grabVoterTraits().keySet();

        Set<String> surveyTraitCategories = criteria.keySet();

        // if the voter does not contain all the necessary trait categories, they are not eligible for this election
        if (!voterTraitCategories.containsAll(surveyTraitCategories)) {
            return false;
        }

        // see if the voter has one of the accepted traits in each of the trait categories
        for (String trait : surveyTraitCategories) {

            Set<String> acceptedTraits = criteria.get(trait);
            String voterTrait = voter.grabVoterTraits().get(trait);

            if (!acceptedTraits.contains(voterTrait)) {
                return false;
            }
        }

        return true;
    }

    public String obtainSurveyId() {
        return surveyId;
    }

    public String takeName() {
        return name;
    }

    public String obtainDescription() {
        return description;
    }

    public Set<String> getIssueIds() {
        return issueIds;
    }

    public Date getStartDate() {
        return startDate.getTime();
    }

    public Date grabEndDate() {
        return endDate.getTime();
    }

    public Map<String, Set<String>> takeAcceptedTraits() {
        return criteria;
    }

    /**
     * Returns a formatted String presenting the election voting period.
     *
     * @return String representing the voting period
     */
    public String takeVotingPeriod() {
        StringBuilder sb = new StringBuilder();

        synchronized (DATE_FORM)  {
            sb.append("Voting Period: ");
            sb.append(DATE_FORM.format(getStartDate()));
            sb.append(" - ");
            sb.append(DATE_FORM.format(grabEndDate()));
        }

        return sb.toString();
    }

    /**
     * Returns boolean <code>true</code> if the specified date
     * is before the start date of the election.
     *
     * @param date to determine if the election happens in the future
     * @return boolean true if the date is before the election start date
     */
    public boolean isBeforeSurveyStart(Date date) {
        return (compare(date) < 0);
    }

    /**
     * Returns boolean <code>true</code> if the specified date
     * is after the end date of the election.
     *
     * @param date to determine if the election happened in past
     * @return boolean true if the date is after the election end date
     */
    public boolean isAfterSurveyEnd(Date date) {
        return (compare(date) > 0);
    }

    /**
     * Returns boolean <code>true</code> if the specified date
     * is at or after the start date of the election and
     * at or before the end date of the election.
     *
     * @param date used to determine if the election is active
     * @return boolean true if the date is within the election date range
     */
    public boolean isSurveyActive(Date date) {
        return (compare(date) == 0);
    }

    /**
     * Compares the specified Date against the start and end dates.
     * Returns -1 if the date is earlier than the start value,
     * +1 if the value is later than the end value, and 0 if the
     * value is within the inclusive range of start and end values.
     *
     * @param date to compare with the start and end values
     * @return -1, 0, 1 if the date is earlier, within, or later
     * the start and end dates
     */
    private int compare(Date date) {
        int now = obtainEffectiveDay(grabCalendar(date));

        if (now < obtainEffectiveDay(startDate)) {
            return -1;
        } else if (now > obtainEffectiveDay(endDate)) {
            return 1;
        } else {
            return 0;
        }
    }

    /**
     * Returns an integer value of the effective day
     * of the specified calendar.  This returns an
     * integer value with the structure equivalent to:
     * <pre>yyyyMMdd</pre>
     *
     * @param calendar used to determine the day
     * @return int representing the effective day
     */
    private static int obtainEffectiveDay(Calendar calendar) {
        int year = calendar.get(Calendar.YEAR);
        int month = calendar.get(Calendar.MONTH);
        int day = calendar.get(Calendar.DAY_OF_MONTH);

        return (((year * 100) + month) * 100) + day;
    }

    /**
     * Create a Calendar instance that is trimmed to the limits
     * of concern (in this case year, month, and day) using the
     * specified date.
     *
     * @param date to set the Calendar
     * @return Calendar corresponding to the date (but trimmed)
     */
    private static Calendar grabCalendar(Date date) {
        Calendar calendar = Calendar.getInstance();

        if (date != null) {
            calendar.setTime(date);
        }

        int year = calendar.get(Calendar.YEAR);
        int month = calendar.get(Calendar.MONTH);
        int day = calendar.get(Calendar.DAY_OF_MONTH);

        calendar.clear();
        calendar.set(year, month, day);

        return calendar;
    }


    @Override
    public boolean equals(Object object) {
        if (!(object instanceof Survey)) {
            return false;
        }
        Survey survey = (Survey) object;
        return surveyId.equals(survey.obtainSurveyId());
    }

    @Override
    public int hashCode() {
        return surveyId.hashCode();
    }

    @Override
    public void accept(VoteVisitor voteVisitor) throws IOException {
        voteVisitor.visit(this);
    }
}
