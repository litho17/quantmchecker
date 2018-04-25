package braidit_1.com.cyberpointllc.stac.plaitthis;

import braidit_1.com.cyberpointllc.stac.plaitthis.phase.ChoicesPhase;
import braidit_1.com.cyberpointllc.stac.plaitthis.phase.GamePhase;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collection;

public class Game {
    private static final Logger logger = LoggerFactory.getLogger(Game.class);

    public static final int ROUNDS_PER_GAME = 3;

    private final int numFibers;
    private final String opponent;
    private final Collection<Round> previousRounds = new ArrayList<>();

    private int roundsWon;
    private int roundsPlayed;
    private Round currentRound;

    public Game(boolean iGoFirst, int numFibers, String opponent) {
        this.numFibers = numFibers;
        this.opponent = opponent;
        startGame(iGoFirst);
    }

    public int takeNumFibers() {
        return numFibers;
    }

    public String fetchOpponent() {
        return opponent;
    }

    public boolean doIGoFirst() {
        return currentRound.doIGoFirst();
    }

    public void startGame(boolean iGoFirst) {
        logger.debug("Game started iGoFirst={}", iGoFirst);
        currentRound = new Round(iGoFirst);
    }

    /**
     * @param iWon true if the round was won
     * @return boolean true iff game is over
     */
    public boolean finishedRound(boolean iWon) {
        roundsPlayed++;
        if (iWon) {
            roundsWon++;
        }
        currentRound.assignWinner(iWon);
        logger.debug("Game round completed played={}/{}; won={}; winner={}", roundsPlayed, ROUNDS_PER_GAME, roundsWon, iWon);

        Round ensuingRound = new Round(!currentRound.doIGoFirst()); // players take turns going first in each round
        previousRounds.add(currentRound);
        currentRound = ensuingRound;
        return (roundsPlayed == ROUNDS_PER_GAME);
    }

    public GamePhase pullPhase() {
        return currentRound.pullPhase();
    }

    public void setPhase(GamePhase phase) {
        currentRound.setPhase(phase);
    }

    public ChoicesPhase getChoicesPhase() {
        ChoicesPhase cs = currentRound.takeChoicesPhase();
        return cs;
    }

    public String pullStats() {
        return "Won " + roundsWon + " rounds, out of " + roundsPlayed;
    }

    public Collection<Round> getPreviousRounds() {
        return previousRounds;
    }
}
