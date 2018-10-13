package simplevote_1.com.cyberpointllc.stac.json.basic;

import java.util.List;
import java.util.StringTokenizer;

public class ItemListHelper {
    private final ItemList itemList;

    public ItemListHelper(ItemList itemList) {
        this.itemList = itemList;
    }

    public void split(String s, String sp, List append, boolean isMultiToken) {
        if (s == null || sp == null)
            return;
        if (isMultiToken) {
            new ItemListHelperCoordinator(s, sp, append).invoke();
        } else {
            itemList.split(s, sp, append);
        }
    }

    public void add(int b, String item) {
        if (item == null)
            return;
        itemList.fetchItems().add(b, item.trim());
    }

    public int size() {
        return itemList.fetchItems().size();
    }

    public void release() {
        itemList.fetchItems().clear();
    }

    private class ItemListHelperCoordinator {
        private String s;
        private String sp;
        private List append;

        public ItemListHelperCoordinator(String s, String sp, List append) {
            this.s = s;
            this.sp = sp;
            this.append = append;
        }

        public void invoke() {
            StringTokenizer tokens = new StringTokenizer(s, sp);
            while (tokens.hasMoreTokens()) {
                append.add(tokens.nextToken().trim());
            }
        }
    }
}