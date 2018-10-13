package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class EditBallotGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public EditBallotGuideCreator assignDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public EditBallotGuide formEditBallotGuide() {
        return new EditBallotGuide(directVoteHelper);
    }
}