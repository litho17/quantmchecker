package braidit_1.com.cyberpointllc.stac.plaitthis.command;

import braidit_1.com.cyberpointllc.stac.plaitthis.PlaitIt;

public class AssignLengthCommandBuilder {
    private PlaitIt plaitIt;

    public AssignLengthCommandBuilder setPlaitIt(PlaitIt plaitIt) {
        this.plaitIt = plaitIt;
        return this;
    }

    public AssignLengthCommand composeAssignLengthCommand() {
        return new AssignLengthCommand(plaitIt);
    }
}