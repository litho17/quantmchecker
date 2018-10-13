package simplevote_1.com.cyberpointllc.stac.webmaster.handler;

public class DefaultGuideCreator {
    private String defaultTrail;

    public DefaultGuideCreator fixDefaultTrail(String defaultTrail) {
        this.defaultTrail = defaultTrail;
        return this;
    }

    public DefaultGuide formDefaultGuide() {
        return new DefaultGuide(defaultTrail);
    }
}