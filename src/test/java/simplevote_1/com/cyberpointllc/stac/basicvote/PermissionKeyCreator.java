package simplevote_1.com.cyberpointllc.stac.basicvote;

public class PermissionKeyCreator {
    private String key;

    public PermissionKeyCreator setKey(String key) {
        this.key = key;
        return this;
    }

    public PermissionKey formPermissionKey() {
        return new PermissionKey(key);
    }
}