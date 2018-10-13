package simplevote_1.com.cyberpointllc.stac.algorithm;

import java.util.LinkedList;

/**
* This Cache is implemented as a linked list to slow things down for side channel purposes
*/
public class Table<T>{

    private LinkedList<T> items = new LinkedList<>();
    private int size;
    private boolean active = false; // are we currently in the mode where we add new items to cache
    private static final int OPENING_TO_RELEASE = 10; // how much of the cache to clear when it's "full"

    private int indexToRelease;

    public Table(int size){
        this.size = size;
        indexToRelease = size;
        for (int p = 0; p <size; p++){
            items.add(null);
        }
    }

    public boolean considerIncluding(int index, T essence){
        if (active) {
            return considerIncludingAid(index, essence);
        } else {
            return false;
        }
    }

    private boolean considerIncludingAid(int index, T essence) {
        if (index >= size){
            while(index >= size){
                formOpening();
            }
            return true;
            }
        items.set(index, essence);
        return true;
    }

    public T obtainEssence(int index){
        if (index < size && index >= 0) {
            return items.get(index);
        } else {
            try{
                T item = items.get(index);
            } catch (Exception e){e.getStackTrace();}
            return null;
        }
    }

    public void defineActive(boolean isOn){
        active = isOn;
    }

    private boolean isFull(){
        return (items.get(size-1)!=null);
    }

    private void formOpening(){
        // double size of cache
        for (int p = size; p <2*size; p++){
            items.add(p, null);
        }
        size *= 2;
        }

    public void print(){
        for (int p = 0; p < items.size(); p++){
            T essence = items.get(p);
            if (essence !=null){
                System.out.println(p + ": " + essence);
            }
        }
    }
}
