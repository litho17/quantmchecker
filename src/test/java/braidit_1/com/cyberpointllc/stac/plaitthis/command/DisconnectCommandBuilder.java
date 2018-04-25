package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;

public class DisconnectCommandBuilder {
    private PlaitIt plaitIt;

    public DisconnectCommandBuilder definePlaitIt(PlaitIt plaitIt) {
        this.plaitIt = plaitIt;
        return this;
    }

    public DisconnectCommand composeDisconnectCommand() {
        return new DisconnectCommand(plaitIt);
    }
}