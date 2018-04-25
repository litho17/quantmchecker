package braidit_1.com.cyberpointllc.stac.plaitthis;

public class GameBuilder {
    private boolean iGoFirst;
    private String opponent;
    private int numFibers;

    public GameBuilder setiGoFirst(boolean iGoFirst) {
        this.iGoFirst = iGoFirst;
        return this;
    }

    public GameBuilder fixOpponent(String opponent) {
        this.opponent = opponent;
        return this;
    }

    public GameBuilder defineNumFibers(int numFibers) {
        this.numFibers = numFibers;
        return this;
    }

    public Game composeGame() {
        return new Game(iGoFirst, numFibers, opponent);
    }
}