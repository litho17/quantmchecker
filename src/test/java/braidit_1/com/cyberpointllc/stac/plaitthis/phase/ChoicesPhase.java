package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

import braidit_1.com.cyberpointllc.stac.plait.Plait;

import java.util.Arrays;
import java.util.Collections;

/**
 * This represents those GameStates where 5 the braid choices need to be tracked -- states SELECTING_LENGTHS, and RECEIVED_BRAID_LENGTHS
 */
public class ChoicesPhase extends GamePhase {
 
    private Plait b1;
    private Plait b2;
    private Plait b3;
    private Plait b4;
    private Plait b5;
    private int count=0;
    private boolean isFinished = false; // marks that braids are ready for final retrieval
    private Integer[] plaitIndices = {1, 2, 3, 4, 5};

    public ChoicesPhase(Phase phase){
        super(phase);
        if (this.matches(Phase.RECEIVED_PLAIT_LENGTHS)){
            prepareForChoices();
        }
    }

    // mark that this state is ready for retrieving final braids
    public void fixFinished(boolean finished) {
        this.isFinished = finished;
    }

    /**
     *
     * @param plaitNum
     * @param plait
     * @return true iff all three braids have been put
     */
    public void putPlait(int plaitNum, Plait plait){
        switch (plaitNum){
            case 1:
                if (b1 == null) {
                    count++;

                }
                b1 = plait;
                break;
            case 2:
                if (b2 == null){
                    count++;
                }
                b2 = plait;
                break;
            case 3:
                if (b3 == null){
                    count++;
                }
                b3 = plait;
                break;
            case 4:
                if (b4 == null) {
                    count++;
                }
                b4 = plait;
                break;
            case 5:
                if (b5 == null){
                    count++;
                }
                b5 = plait;
                break;
        }

    }

    public Plait fetchPlait(int plaitNum){
        switch(plaitNum){
            case 1: {
                return b1;
            }
            case 2: {
                return b2;
            }
            case 3:{
                return b3;
            }
            case 4:{
                return b4;
            }
            case 5:{
                return b5;
            }
            default:
                throw new IllegalArgumentException("Selection must be 1, 2, 3, 4, or 5");
        }
    }

    private void prepareForChoices(){
        Collections.shuffle(Arrays.asList(plaitIndices), Plait.random);
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        for (int q = 1; q <=5; q++) {
            builder.append(fetchPlait(q));
            builder.append(", ");
        }
        return builder.toString();
    }
}
