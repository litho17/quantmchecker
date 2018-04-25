package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

public class PlaitSelectedStepBuilder {
    private GamePhase.Phase step;

    public PlaitSelectedStepBuilder fixAdvance(GamePhase.Phase advance) {
        this.step = advance;
        return this;
    }

    public PlaitSelectedPhase composePlaitSelectedStep() {
        return new PlaitSelectedPhase(step);
    }
}