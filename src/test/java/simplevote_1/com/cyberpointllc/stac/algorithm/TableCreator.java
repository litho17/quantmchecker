package simplevote_1.com.cyberpointllc.stac.algorithm;

public class TableCreator<T> {
    private int size;

    public TableCreator setSize(int size) {
        this.size = size;
        return this;
    }

    public Table formTable() {
        return new Table(size);
    }
}