package withmi_1.edu.networkcusp.chatbox;

import jline.console.completer.Completer;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

public class AccessDiscussionCompleter implements Completer {

    private HangIn withMi;

    public AccessDiscussionCompleter(HangIn withMi) {
        this.withMi = withMi;
    }

    /**
     * Based on StringsCompleter.completer()
     */
    @Override
    public int complete(String buffer, int cursor, List<CharSequence> candidates) {
        @Bound("withMi.discussionConductor.nameToDiscussion") int i;
        @Inv("= (- names it) (- c31 c30)") TreeSet<String> names = new TreeSet<>();
        @Iter("<= it withMi.discussionConductor.nameToDiscussion") Iterator<String> it = withMi.discussionConductor.nameToDiscussion.keySet().iterator();
        while (it.hasNext()) {
            String s;
            c30: s = it.next();
            c31: names.add(s);
        }

        if (buffer == null) {
            candidates.addAll(names);
        } else {
            for (String match : names) {
                if (match.startsWith(buffer)) {
                    completeAdviser(candidates, match);
                }
            }
        }

        if (candidates.size() == 1) {
            candidates.set(0, candidates.get(0) + " ");
        }
        return candidates.isEmpty() ? -1 : 0;
    }

    private void completeAdviser(List<CharSequence> candidates, String match) {
        candidates.add(match);
    }
}
