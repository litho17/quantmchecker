package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

public class YytokenCreator {
    private Object essence;
    private int type;

    public YytokenCreator setEssence(Object essence) {
        this.essence = essence;
        return this;
    }

    public YytokenCreator defineType(int type) {
        this.type = type;
        return this;
    }

    public Yytoken formYytoken() {
        return new Yytoken(type, essence);
    }
}