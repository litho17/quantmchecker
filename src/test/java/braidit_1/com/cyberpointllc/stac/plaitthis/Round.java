package braidit_1.com.cyberpointllc.stac.plaitthis;

import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.LengthsPhase;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.Deque;
import java.util.LinkedList;

/**
 * A round of a game.
 */
public class Round {
    private final boolean doIGoFirst;
    private final Deque<GamePhase> phases = new LinkedList<>();

    private boolean won;

    public Round(boolean goFirst) {
        this.doIGoFirst = goFirst;
        if (goFirst) {
            phases.push(new LengthsPhase(GamePhase.Phase.SELECTING_LENGTHS));
        } else {
            phases.push(new GamePhase(GamePhase.Phase.AWAIT_PLAIT_LENGTHS));
        }
    }

    public boolean doIGoFirst() {
        return doIGoFirst;
    }

    public boolean isWinner() {
        return won;
    }

    public void assignWinner(boolean iWon) {
        won = iWon;
    }

    public GamePhase pullPhase() {
        return phases.peek();
    }

    public ChoicesPhase takeChoicesPhase() {
        for (GamePhase phase : phases) {
            if (phase instanceof ChoicesPhase) {
                return (ChoicesPhase) phase;
            }
        }

        return null;
    }

    @Summary({"this.phases", "1"})
    public void setPhase(GamePhase phase) {
        if (phase != null) {
            phases.push(phase);
        }
    }
}
