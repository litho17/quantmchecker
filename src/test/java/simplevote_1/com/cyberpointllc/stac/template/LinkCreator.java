package simplevote_1.com.cyberpointllc.stac.template;

public class LinkCreator {
    private String name;
    private String url;

    public LinkCreator fixName(String name) {
        this.name = name;
        return this;
    }

    public LinkCreator assignUrl(String url) {
        this.url = url;
        return this;
    }

    public Link formLink() {
        return new Link(url, name);
    }
}