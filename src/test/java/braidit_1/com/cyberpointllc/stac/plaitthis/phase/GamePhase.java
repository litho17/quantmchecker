package braidit_1.com.cyberpointllc.stac.plaitthis.phase;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

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
    private static @InvUnk("Non-constant increment") Map<Phase, List<String>> allowedCommands = new HashMap<>();

    private static String errorPhase;

    static {
        Phase[] cores = Phase.values();
        for (int a = 0; a < cores.length; ) {
            while ((a < cores.length) && (Math.random() < 0.6)) {
                for (; (a < cores.length) && (Math.random() < 0.4); ) {
                    for (; (a < cores.length) && (Math.random() < 0.5); ) {
                        Phase s = cores[a];
                        c41: allowedCommands.put(s, fetchCommands(s));
                        c42: a++;
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
        @Inv("= self (+ c82 c85 c91 c92 c95 c96 c99 c100 c101 c107 c108 c111 c112 c113 c114 c115 c116 c117 c118 c124 c125 c133)") List<String> commands = new ArrayList<>();
        switch (phase) {
            case IDLE:
                c82: commands.add("connect");
                break;
            case CONNECTED:
                c85: commands.add("offer_game");
                break;
            case GAME_OFFERED:
                // No other commands; awaiting a response
                break;
            case OFFER_RECEIVED:
                c91: commands.add("accept_game");
                c92: commands.add("decline_game");
                break;
            case SELECTING_LENGTHS:
                c95: commands.add("set_length");
                c96: commands.add("print");
                break;
            case LENGTHS_SELECTED:
                c99: commands.add("set_length"); // can update one of the created braids
                c100: commands.add("send_lengths");
                c101: commands.add("print");
                break;
            case AWAIT_PLAIT_LENGTHS:
                // can only wait
                break;
            case RECEIVED_PLAIT_LENGTHS:
                c107: commands.add("select_braid");
                c108: commands.add("print");
                break;
            case PLAIT_SELECTED:
                c111: commands.add("select_braid"); // can change your mind
                c112: commands.add("modify_random");
                c113: commands.add("swap");
                c114: commands.add("triple_swap");
                c115: commands.add("expand3");
                c116: commands.add("expand5");
                c117: commands.add("send_modified");
                c118: commands.add("print");
                break;
            case AWAIT_MODIFIED_PLAIT:
                // can only wait
                break;
            case RECEIVED_MODIFIED_PLAIT:
                c124: commands.add("make_guess");
                c125: commands.add("print");
                break;
            case AWAIT_OUTCOME:
                // can only wait
                break;
        }
        // can disconnect as long as we're connected
        if (phase != Phase.IDLE) {
            c133: commands.add("disconnect");
        }
        return commands;
    }

    @Override
    public String toString() {
        return phase.name();
    }
}