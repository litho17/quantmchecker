package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

public class LengthsPhase extends GamePhase {
    private int count=0;
    private int length1 = -1;
    private int length2 = -1;
    private int length3 = -1;
    private int length4 = -1;
    private int length5 = -1;
    
    public LengthsPhase(Phase phase){
        super(phase);
    }
    
    public boolean placeLength(int index, int length) {
        switch (index){
            case 1:
                if (length1 == -1) {
                    count++;
                }
                length1 = length;
                break;
            case 2:
                if (length2 == -1){
                    count++;
                }
                length2 = length;
                break;
            case 3:
                if (length3 == -1){
                    count++;
                }
                length3 = length;
                break;
            case 4:
                if (length4 == -1) {
                    count++;
                }
                length4 = length;
                break;
            case 5:
                if (length5 == -1){
                    count++;
                }
                length5 = length;
                break;
        }

        if (count == 5) {
            phase = Phase.LENGTHS_SELECTED;
            return true;
        } else {
            return false;
        }
    }

    public int grabLength(int plaitNum){
        switch(plaitNum){
            case 1: {
                return length1;
            }
            case 2: {
                return length2;
            }
            case 3:{
                return length3;
            }
            case 4:{
                return length4;
            }
            case 5:{
                return length5;
            }
            default:
                throw new IllegalArgumentException("Selection must be 1, 2, 3, 4, or 5");
        }
    }
}
