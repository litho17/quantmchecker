package battleboats_1.com.cyberpointllc.stac.battleship.stages;

import java.util.Arrays;
import java.util.List;

public enum Stage {
    IDLE("connect"),
    CONNECTED("offer_game", "disconnect"),
    COMPETITION_OFFERED("offer_game", "disconnect"),
    OFFER_RECEIVED("accept_game", "decline_game", "disconnect"),
    LAY_SHIPS("print", "place_battleship", "place_carrier", "place_destroyer", "place_cruiser", "place_submarine", "place_cannon", "place_all", "disconnect"),
    LAY_SHIPS_AND_FINISH("print", "place_battleship", "place_carrier", "place_destroyer", "place_cruiser", "place_submarine", "place_cannon", "end_placing_boats", "place_all", "disconnect"),
    IM_READY("print", "disconnect"),
    WAIT_FOR_OPPONENT_READY("print", "disconnect"),
    DECLARE_FIRE("print", "shoot", "disconnect", "shot_help"),
    WAIT_FOR_REPORT("print", "disconnect"),
    WAIT_FOR_FIRE("print", "disconnect");

    public final List<String> commands;

    Stage(String... commands) {
        this.commands = Arrays.asList(commands);
    }

    public List<String> takeCommands() {
        return commands;
    }
}
