package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

import braidit_1.com.cyberpointllc.stac.plait.Plait;

/**
 * This represents those game states where there is a single braid to be tracked -- states BRAID_SELECTED, and RECEIVED_MODIFIED_BRAID
 */
public class PlaitSelectedPhase extends GamePhase {
    private Plait plait;
    private int plaitCount; // which braid was selected

    public PlaitSelectedPhase(Phase phase) {
          super(phase);
    }

    public void insertPlait(Plait plait) {
        this.plait = plait;
        this.plaitCount = 1;
    }

    // this method specifies the index of the braid selected
    public void insertPlait(Plait plait, int plaitNum) {
        if (plaitNum <= 0 ||  plaitNum > 5) {
            throw new IllegalArgumentException("Selected braid index out of range");
        }
        this.plait = plait;
        this.plaitCount = plaitNum;
    }

    public Plait obtainPlait() {
        return plait;
    }

    public String getPlaitString() {
        String plaitStr = plait.takeMeetings();
        return String.format("%1$-" + plaitCount * plait.MAX_LENGTH + "s", plaitStr);
        }
}
