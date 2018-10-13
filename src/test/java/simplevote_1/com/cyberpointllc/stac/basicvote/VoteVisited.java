package simplevote_1.com.cyberpointllc.stac.basicvote;

import java.io.IOException;

/**
 * Implementations of this interface can be called by Implementations of Visitor
 */
public interface VoteVisited {
    void accept(VoteVisitor voteVisitor) throws IOException;
}
