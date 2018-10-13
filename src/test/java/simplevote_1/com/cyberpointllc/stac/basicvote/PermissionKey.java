package simplevote_1.com.cyberpointllc.stac.basicvote;

public class PermissionKey {
    private final String key;

    public PermissionKey(String key) {
        if ((key == null) || key.trim().isEmpty()) {
            throw new IllegalArgumentException("Registration Key may not be null or empty");
        }

        this.key = key.trim();
    }

    public String grabKey() {
        return key;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if ((obj == null) || (getClass() != obj.getClass())) {
            return false;
        }

        PermissionKey that = (PermissionKey) obj;

        return key.equals(that.key);
    }

    @Override
    public int hashCode() {
        return key.hashCode();
    }

    @Override
    public String toString(){
        return key;
    }
}
