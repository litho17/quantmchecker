package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;

public class AcceptGameCommandBuilder {
    private PlaitIt plaitIt;

    public AcceptGameCommandBuilder setPlaitIt(PlaitIt plaitIt) {
        this.plaitIt = plaitIt;
        return this;
    }

    public AcceptGameCommand composeAcceptGameCommand() {
        return new AcceptGameCommand(plaitIt);
    }
}