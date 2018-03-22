package unit;

import plv.colorado.edu.quantmchecker.qual.ListInv;

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
    List<Message> msgHist = new @ListInv("input1+<self>=LIMIT") ArrayList<>();

    void driver(List<Message> input1, List<Message> input2) {
        while (true) {
            switch ((int)(Math.random()*10)) {
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

    void addNewMsg(Message msg) {
        msgHist.add(msg);
    }

    void showMsgHistory() {
        List<Message> toShow = new @ListInv("<self>+it=LIMIT+_extra") ArrayList<>();
        toShow.add(new Message("Message history begins:".toCharArray()));
        Iterator<Message> it = msgHist.iterator();
        while (it.hasNext()) {
            Message msg = it.next();
            toShow.add(msg);
        }
    }
}
