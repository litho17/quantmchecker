package withmi_1.edu.networkcusp.chatbox;

import jline.console.completer.Completer;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.List;
import java.util.TreeSet;

public class MemberCompleter implements Completer {
    private HangIn withMi;

    public MemberCompleter(HangIn withMi) {
        this.withMi = withMi;
    }

    /**
     * Based on StringsCompleter.completer()
     */
    @Override
    public int complete(String buffer, int cursor, List<CharSequence> candidates) {
        @Bound("withMi.memberConductor.idToMember") int i;
        @Inv("= (- names j) (- c27 c28)") TreeSet<String> names = new TreeSet<>();
        for (@Iter("<= j withMi.memberConductor.idToMember") int j = 0; j < withMi.memberConductor.idToMember.size();) {
            WithMiUser member = withMi.memberConductor.idToMember.get(j);
            c27: names.add(member.obtainName());
            c28: j = j + 1;
        }

        if (buffer == null) {
            completeSupervisor(candidates, names);
        } else {
            for (String match : names) {
                completeCoordinator(buffer, candidates, match);
            }
        }

        if (candidates.size() == 1) {
            candidates.set(0, candidates.get(0) + " ");
        }

        return candidates.isEmpty() ? -1 : 0;
    }

    private void completeCoordinator(String buffer, List<CharSequence> candidates, String match) {
        if (match.startsWith(buffer)) {
            candidates.add(match);
        }
    }

    private void completeSupervisor(List<CharSequence> candidates, TreeSet<String> names) {
        candidates.addAll(names);
    }
}
