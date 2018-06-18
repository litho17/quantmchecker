package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

import plv.colorado.edu.quantmchecker.qual.Inv;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Represents the state of the game in progress
 */
public class GamePhase {
    public enum Phase {
        IDLE,
        CONNECTED,
        GAME_OFFERED,
        OFFER_RECEIVED,
        SELECTING_LENGTHS,
        LENGTHS_SELECTED,
        AWAIT_PLAIT_LENGTHS,
        RECEIVED_PLAIT_LENGTHS,
        PLAIT_SELECTED,
        AWAIT_MODIFIED_PLAIT,
        RECEIVED_MODIFIED_PLAIT,
        AWAIT_OUTCOME
    }

    // map each state to the set of allowed commands in that state
    private static @Inv("+allowedCommands=-a+c41-c39") Map<Phase, List<String>> allowedCommands = new HashMap<>();

    private static String errorPhase;

    static {
        Phase[] cores = Phase.values();
        for (int a = 0; a < cores.length; ) {
            while ((a < cores.length) && (Math.random() < 0.6)) {
                for (; (a < cores.length) && (Math.random() < 0.4); ) {
                    c39: for (; (a < cores.length) && (Math.random() < 0.5); a++) {
                        Phase s = cores[a];
                        c41: allowedCommands.put(s, fetchCommands(s));
                    }
                }
            }
        }

        errorPhase = null;
        }

    protected Phase phase;

    public GamePhase(Phase step) {
        this.phase = step;
    }

    public Phase getStep() {
        return phase;
    }

    public boolean matches(Phase phase) {
        return this.phase == phase;
    }

    public static void fixErrorStep(String errorType) {
        errorPhase = errorType;
    }

    public static String grabErrorStep(){
        return errorPhase;
    }

    public List<String> obtainAllowedCommands() {
        return allowedCommands.get(phase);
    }

    // associate allowed commands with each state (note: this doesn't include commands that are always available, such as
    // help, history, and exit.
    private static List<String> fetchCommands(Phase phase) {
        List<String> commands = new ArrayList<>();
        switch (phase) {
            case IDLE:
                commands.add("connect");
                break;
            case CONNECTED:
                commands.add("offer_game");
                break;
            case GAME_OFFERED:
                // No other commands; awaiting a response
                break;
            case OFFER_RECEIVED:
                commands.add("accept_game");
                commands.add("decline_game");
                break;
            case SELECTING_LENGTHS:
                commands.add("set_length");
                commands.add("print");
                break;
            case LENGTHS_SELECTED:
                commands.add("set_length"); // can update one of the created braids
                commands.add("send_lengths");
                commands.add("print");
                break;
            case AWAIT_PLAIT_LENGTHS:
                // can only wait
                break;
            case RECEIVED_PLAIT_LENGTHS:
                commands.add("select_braid");
                commands.add("print");
                break;
            case PLAIT_SELECTED:
                commands.add("select_braid"); // can change your mind
                commands.add("modify_random");
                commands.add("swap");
                commands.add("triple_swap");
                commands.add("expand3");
                commands.add("expand5");
                commands.add("send_modified");
                commands.add("print");
                break;
            case AWAIT_MODIFIED_PLAIT:
                // can only wait
                break;
            case RECEIVED_MODIFIED_PLAIT:
                commands.add("make_guess");
                commands.add("print");
                break;
            case AWAIT_OUTCOME:
                // can only wait
                break;
        }
        // can disconnect as long as we're connected
        if (phase != Phase.IDLE) {
            commands.add("disconnect");
        }
        return commands;
    }

    @Override
    public String toString() {
        return phase.name();
    }
}