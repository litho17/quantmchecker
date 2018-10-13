package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class ConfirmationGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public ConfirmationGuideCreator fixDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public ConfirmationGuide formConfirmationGuide() {
        return new ConfirmationGuide(directVoteHelper);
    }
}