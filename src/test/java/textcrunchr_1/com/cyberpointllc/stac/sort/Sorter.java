package textcrunchr_1.com.cyberpointllc.stac.sort;

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
    @Summary({"Unverified (API)"})
    public List<T> sort(Collection<T> stuff) {
        List<T> stuffList = new ArrayList(stuff);
        Collections.sort(stuffList, comparator);
        return stuffList;
    }
}
