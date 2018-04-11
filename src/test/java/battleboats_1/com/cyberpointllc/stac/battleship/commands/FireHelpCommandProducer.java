package battleboats_1.com.cyberpointllc.stac.battleship.commands;

import battleboats_1.com.cyberpointllc.stac.battleship.WarShips;

public class FireHelpCommandProducer {
    private WarShips warShips;

    public FireHelpCommandProducer fixWarShips(WarShips warShips) {
        this.warShips = warShips;
        return this;
    }

    public FireHelpCommand makeFireHelpCommand() {
        return new FireHelpCommand(warShips);
    }
}