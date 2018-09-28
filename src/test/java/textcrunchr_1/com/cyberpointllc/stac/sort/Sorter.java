package textcrunchr_1.com.cyberpointllc.stac.sort;

import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.*;

public class Sorter<T> {

    private final Comparator<T> comparator;

    public Sorter(Comparator<T> comparator) {
        this.comparator = comparator;
    }

    /**
     * return a List containing the elements of stuff, ordered by class T's natural ordering
     */
    public List<T> sort(Collection<T> stuff) {
        @InvUnk("Unknown API") List<T> stuffList = new ArrayList(stuff);
        Collections.sort(stuffList, comparator);
        return stuffList;
    }
}
