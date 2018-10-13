package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;

/**
 * A serialization visitor that visits most SimpleVote classes
 * and serializes the instances of those classes.
 * <p>
 * Should coordinate with the DeserializeVisitor
 */
public interface VoteVisitor {
    void visit(Reply reply) throws IOException;

    void visit(Issue issue) throws IOException;

    void visit(Choice choice) throws IOException;

    void visit(Ballot ballot) throws IOException;

    void visit(Survey survey) throws IOException;

    void visit(Voter voter) throws IOException;

    void visit(SurveyOutcomes surveyOutcomes) throws IOException;
}
