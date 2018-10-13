package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class IconGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public IconGuideCreator assignDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public IconGuide formIconGuide() {
        return new IconGuide(directVoteHelper);
    }
}