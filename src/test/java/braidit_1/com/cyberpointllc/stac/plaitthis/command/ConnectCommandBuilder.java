package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;

public class ConnectCommandBuilder {
    private PlaitIt plaitIt;

    public ConnectCommandBuilder fixPlaitIt(PlaitIt plaitIt) {
        this.plaitIt = plaitIt;
        return this;
    }

    public ConnectCommand composeConnectCommand() {
        return new ConnectCommand(plaitIt);
    }
}