package braidit_1.com.cyberpointllc.stac;

import braidit_1.com.cyberpointllc.stac.plaitthis.command.*;
import org.apache.commons.cli.CommandLine;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;
import java.util.Queue;

/**
 * @author Tianhan Lu
 */
public class Driver {
    PrintStream out;
    CommandLine cmdLine;
    public void main(List<CommandLine> input) {
        @Inv("= (- acceptGameCommand.plaitIt.currentGame.currentRound.phases it) (- c32 c30)") AcceptGameCommand acceptGameCommand = null;
        @Inv("= (- assignLengthCommand.plaitIt.currentGame.currentRound.phases it) (- c34 c30)") AssignLengthCommand assignLengthCommand = null;
        @Inv("= (- declineGameCommand.plaitIt.currentGame.currentRound.phases it) (- c36 c30)") DeclineGameCommand declineGameCommand = null;
        @Inv({"= (- makeGuessCommand.plaitIt.currentGame.previousRounds it it) (- (+ c38 c38) c30 c30)", "= (- makeGuessCommand.plaitIt.currentGame.currentRound.phases it) (- c38 c30)"}) MakeGuessCommand makeGuessCommand = null;
        @Inv("= (- offerGameCommand.plaitIt.currentGame.currentRound.phases it) (- c40 c30)") OfferGameCommand offerGameCommand = null;
        @Inv("= (- selectPlaitCommand.plaitIt.currentGame.currentRound.phases it) (- c42 c30)") SelectPlaitCommand selectPlaitCommand = null;
        @Inv("= (- transmitLengthsCommand.plaitIt.currentGame.currentRound.phases it) (- c44 c30)") TransmitLengthsCommand transmitLengthsCommand = null;
        @Inv("= (- transmitModifiedPlaitCommand.plaitIt.currentGame.currentRound.phases it) (- c46 c30)") TransmitModifiedPlaitCommand transmitModifiedPlaitCommand = null;
        @Bound("* 10 input") int i;
        @Iter("<= it input") Iterator<CommandLine> it = input.iterator();
        while(true) {
            c30: cmdLine = it.next();
            c32: acceptGameCommand.execute(out, cmdLine);
            c34: assignLengthCommand.execute(out, cmdLine);
            c36: declineGameCommand.execute(out, cmdLine);
            c38: makeGuessCommand.execute(out, cmdLine);
            c40: offerGameCommand.execute(out, cmdLine);
            c42: selectPlaitCommand.execute(out, cmdLine);
            c44: transmitLengthsCommand.execute(out, cmdLine);
            c46: transmitModifiedPlaitCommand.execute(out, cmdLine);
        }
    }
}
