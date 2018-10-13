package simplevote_1.com.cyberpointllc.stac.basicvote.handler;

public class PermissionAssessGuideCreator {
    private DirectVoteHelper directVoteHelper;

    public PermissionAssessGuideCreator setDirectVoteHelper(DirectVoteHelper directVoteHelper) {
        this.directVoteHelper = directVoteHelper;
        return this;
    }

    public PermissionAssessGuide formPermissionAssessGuide() {
        return new PermissionAssessGuide(directVoteHelper);
    }
}