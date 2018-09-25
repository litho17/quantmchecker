package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;

public class MakeGuessCommandBuilder {
    private PlaitIt plaitIt;

    public MakeGuessCommandBuilder definePlaitIt(PlaitIt plaitIt) {
        this.plaitIt = plaitIt;
        return this;
    }

    public MakeGuessCommand composeMakeGuessCommand() {
        return new MakeGuessCommand(plaitIt);
    }
}