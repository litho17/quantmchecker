package unit;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
class Message {
    char[] msg = new char[200];

    public Message(char[] msg) {
        System.arraycopy(msg, 0, this.msg, 0, 200);
        // this.msg = msg; // this should not type check!
    }
}

public class MotivatingExample {
    @Inv("input1+<self>=+30-29") List<Message> msgHist = new ArrayList<>();

    void driver(List<Message> input1, List<Message> input2) {
        while (true) {
            switch ((int) (Math.random() * 10)) {
                case 1:
                    Message msg = input1.remove(0);
                    addNewMsg(msg);
                    break;
                case 2:
                    input2.remove(0);
                    showMsgHistory();
                    break;
                default:
            }
        }
    }

    @Summary("this.msg++") void addNewMsg(Message msg) {
        msgHist.add(msg);
    }

    void showMsgHistory() {
        @Inv("it+<self>=+51-50") List<Message> toShow = new ArrayList<>();
        toShow.add(new Message("Message history begins:".toCharArray()));
        Iterator<Message> it = msgHist.iterator();
        while (it.hasNext()) {
            Message msg = it.next();
            toShow.add(msg);
        }
    }
}
