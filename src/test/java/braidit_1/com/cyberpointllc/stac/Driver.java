package braidit_1.com.cyberpointllc.stac;

import braidit_1.com.cyberpointllc.stac.plaitthis.command.*;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.Queue;

/**
 * @author Tianhan Lu
 */
public class Driver {
    PrintStream out;
    CommandLine cmdLine;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c32") AcceptGameCommand c1;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c34") AssignLengthCommand c2;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c36") DeclineGameCommand c3;
    @Inv({"= self.plaitIt.currentGame.previousRounds (+ c38 c38)", "= self.plaitIt.currentGame.currentRound.phases c38"}) MakeGuessCommand c4;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c40") OfferGameCommand c5;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c42") SelectPlaitCommand c6;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c44") TransmitLengthsCommand c7;
    @Inv("= self.plaitIt.currentGame.currentRound.phases c46") TransmitModifiedPlaitCommand c8;
    public void main() {
        @Input("100") int input = 0;
        String c;
        while (true) {
            input = input - 1;
            if (Math.random() > 0.8) {
                c32: c1.execute(out, cmdLine);
            } else if (Math.random() > 0.7) {
                c34: c2.execute(out, cmdLine);
            } else if (Math.random() > 0.6) {
                c36: c3.execute(out, cmdLine);
            } else if (Math.random() > 0.5) {
                c38: c4.execute(out, cmdLine);
            } else if (Math.random() > 0.4) {
                c40: c5.execute(out, cmdLine);
            } else if (Math.random() > 0.3) {
                c42: c6.execute(out, cmdLine);
            } else if (Math.random() > 0.2) {
                c44: c7.execute(out, cmdLine);
            } else if (Math.random() > 0.1) {
                c46: c8.execute(out, cmdLine);
            } else {
                ;
            }
        }
    }
}
