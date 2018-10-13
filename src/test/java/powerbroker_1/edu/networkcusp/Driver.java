package powerbroker_1.edu.networkcusp;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import powerbroker_1.edu.networkcusp.buyOp.Auction;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.OfferConveyData;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.PromiseData;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsPublicIdentity;

import java.util.Iterator;
import java.util.List;

/**
 * @author Tianhan Lu
 */
public class Driver {
    ProtocolsPublicIdentity customer;
    PromiseData contract;
    OfferConveyData contract_;
    ProtocolsPublicIdentity myIdentity;
    public void main(List<Object> input) throws Exception {
        @Bound("* 5 input") int i;
        @Inv("and (= (- auction.biddersStatus.biddersNotReported it it it) (- (+ c28 c29 c29) c27 c27 c27)) (= (- auction.proposals it it) (- (+ c28 c29) c27 c27)) (= (- auction.biddersStatus.conceders it) (- c30 c27)) (= auction.biddersStatus.claimedWinners 0) (= auction.biddersStatus.conceders auction.proposals 0)") Auction auction = null;
        @Iter("<= it input") Iterator<Object> it = input.iterator();
        while (it.hasNext()) {
            Object o;
            c27: o = it.next();
            c28: auction.addContract(customer, contract);
            c29: auction.recordMyCommit(contract_, myIdentity);
            c30: auction.addConcession(customer);
        }
    }
}
