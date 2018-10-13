package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class ShowResponsesGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public ShowResponsesGuideCreator setDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public ShowResponsesGuide formShowResponsesGuide() {
        return new ShowResponsesGuide(directVoteHelper);
    }
}