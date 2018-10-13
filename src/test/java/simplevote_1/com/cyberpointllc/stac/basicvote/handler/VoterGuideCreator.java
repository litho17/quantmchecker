package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class VoterGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public VoterGuideCreator assignDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public VoterGuide formVoterGuide() {
        return new VoterGuide(directVoteHelper);
    }
}