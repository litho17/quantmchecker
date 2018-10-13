package powerbroker_1.edu.networkcusp.broker.step;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsConnection;
import powerbroker_1.edu.networkcusp.broker.PurchasePlan;
import powerbroker_1.edu.networkcusp.broker.MyAuction;
import powerbroker_1.edu.networkcusp.broker.ProductIntermediaryAuction;
import powerbroker_1.edu.networkcusp.broker.ProductIntermediaryRaiser;
import powerbroker_1.edu.networkcusp.broker.Powerbrokermsg;
import powerbroker_1.edu.networkcusp.broker.buyOp.AuctionAdapter;
import powerbroker_1.edu.networkcusp.logging.Logger;
import powerbroker_1.edu.networkcusp.logging.LoggerFactory;

import java.util.ArrayList;
import java.util.List;

public class ResultsStage extends AuctionBaseStage {

    private final Logger logger = LoggerFactory.pullLogger(getClass());

    private final PurchasePlan offerPlan;
    private final AuctionAdapter auctionAdapter;

    /**
     *
     * @param auctions the entire list of auctions that we'll be processing at some point.  For the purposes of this
     *                 phase (and most others) we're only every concerned with the first auction on this list. That's
     *                 the 'current' auction.
     * @param myAuctions a list of auctions that I've started.
     * @param offerPlan the bidding plan that indicates what we should try to do.
     * @param auctionAdapter used to help us manage the current auction and the auction library.
     * @param stageOverseer
     */
    public ResultsStage(List<ProductIntermediaryAuction> auctions, List<MyAuction> myAuctions, PurchasePlan offerPlan, AuctionAdapter auctionAdapter, StageOverseer stageOverseer) {
        super(auctions, myAuctions, stageOverseer);
        this.offerPlan = offerPlan;
        this.auctionAdapter = auctionAdapter;
    }

    @Override
    public void enterStage() throws ProductIntermediaryRaiser {
        super.enterStage();

        AuctionAdapter.Winner winner = auctionAdapter.takeWinner();

        if (winner.winnerId.equals(takeStageOverseer().takeIdentity().pullId())) {
            logger.info("I won. bid: " + winner.offer);
        } else {
            String id = winner.winnerId;
            if (id.length() > 25){
                id = id.substring(0, 25) + "...";
            }
            logger.info(id + " won. bid: " + winner.offer);
        }

        if (isItMyTurnToSendMessages()) {
            enterStageGuide();
        }
    }

    private void enterStageGuide() throws ProductIntermediaryRaiser {
        new ResultsStageGuide().invoke();
    }

    @Override
    public Stage handleMsg(ProtocolsConnection connection, Powerbrokermsg.BaseMessage msg) throws ProductIntermediaryRaiser {
        if (msg.getType() == Powerbrokermsg.BaseMessage.Type.RESULTS_END) {

            logger.info("recevied RESULTS_END from " + connection.takeTheirIdentity().obtainTruncatedId());

            addFinalMessage(connection.takeTheirIdentity(), msg);

            if (isItMyTurnToSendMessages()) {
                handleMsgHelper();
            }

            return shouldTransitionToNextStage();
        } else {
            return handleMsgSupervisor(msg);
        }
    }

    private Stage handleMsgSupervisor(Powerbrokermsg.BaseMessage msg) {
        logger.error("Invalid message type in ResultsPhase: " + msg.getType());
        return null;
    }

    private void handleMsgHelper() throws ProductIntermediaryRaiser {
        sendResultsEndMessage();
    }

    private void sendResultsEndMessage() throws ProductIntermediaryRaiser {
        logger.info("Sending results end message");
        Powerbrokermsg.BaseMessage baseMessage = Powerbrokermsg.BaseMessage.newBuilder()
                .setType(Powerbrokermsg.BaseMessage.Type.RESULTS_END)
                .build();

        sendFinalMessage(baseMessage.toByteArray());
    }

    @Override
    protected Stage nextStage() throws ProductIntermediaryRaiser {
        ProductIntermediaryAuction curAuction = getCurrentAuction();

        AuctionAdapter.Winner winner = auctionAdapter.takeWinner();
        if (winner.winnerId.equals(takeStageOverseer().takeIdentity().pullId())) {
            nextStageAdviser(curAuction, winner);
        }

        if (isCurAuctionMyAuction()) {
            // we sold this power, tell someone
            takeStageOverseer().takeProductIntermediaryCustomer().soldProduct(curAuction.productAmount, winner.offer, winner.winnerId);
        }

        // we need a new bid plan, if we're the seller we remove the sell action
        // if we've won (and we're not the seller) we remove the buy
        PurchasePlan newOfferPlan = new PurchasePlan(offerPlan);

        String myId = takeStageOverseer().takeIdentity().pullId();

        if (winner.winnerId.equals(myId)) {
            if (!isCurAuctionMyAuction()) {
                // we only bought power if we weren't the seller...
                newOfferPlan.bought(curAuction.productAmount, winner.offer);
            }
        }
        if (isCurAuctionMyAuction()) {
            if (!winner.winnerId.equals(myId)) {
                nextStageGuide(curAuction, winner, newOfferPlan);
            }
        }

        takeStageOverseer().assignOfferPlan(newOfferPlan);

        // if there are more announced auctions, we need to process them, otherwise we go back to announce phase
        @Bound("+ auctions myAuctions") int k;
        if (auctions.size() > 1) {
            @Inv("= (- newAuctions a) (- c142 c143)") List<ProductIntermediaryAuction> newAuctions = new ArrayList<>(auctions.size() - 1);
            for (@Iter("<= a auctions") int a = 1; a < auctions.size(); ) {
                c142: newAuctions.add(auctions.get(a));
                c143: a = a + 1;
            }

            @Inv("= (- newMyAuctions q) (- c157 c162)") List<MyAuction> newMyAuctions = new ArrayList<>();
            // add all my auctions, but skip the current auction if it's one we bid on
            // We use this variable in case there are two different auctions
            // with the same id. We only want to skip one auction
            boolean foundCurAuction = false;
            for (@Iter("<= q myAuctions") int q = 0; q < myAuctions.size(); ) {
                for (; (q < myAuctions.size()) && (Math.random() < 0.4); ) {
                    for (; (q < myAuctions.size()) && (Math.random() < 0.4); ) {
                        for (; (q < myAuctions.size()) && (Math.random() < 0.6);) {
                            MyAuction curMyAuction = myAuctions.get(q);
                            if (!curAuction.id.equals(curMyAuction.getId()) || foundCurAuction) {
                                c157: newMyAuctions.add(curMyAuction);
                            } else {
                                // we found the current auction
                                foundCurAuction = true;
                            }
                            c162: q = q + 1;
                        }
                    }
                }
            }

            // tell the user their current bid plan
            takeStageOverseer().takeProductIntermediaryCustomer().resultsCalculated(newOfferPlan);


            logger.info("Moving to begin phase");
            return new AuctionBeginStage(newAuctions, newMyAuctions, takeStageOverseer());
        } else {

            // we're done, let the user know
            return nextStageEngine(newOfferPlan);
        }
    }

    private Stage nextStageEngine(PurchasePlan newOfferPlan) {
        takeStageOverseer().takeProductIntermediaryCustomer().auctionSequenceComplete(newOfferPlan);

        logger.info("Moving to disconnect phase");
        return new DisconnectStage(takeStageOverseer());
    }

    private void nextStageGuide(ProductIntermediaryAuction curAuction, AuctionAdapter.Winner winner, PurchasePlan newOfferPlan) {
        newOfferPlan.sold(curAuction.productAmount, winner.offer);
    }

    private void nextStageAdviser(ProductIntermediaryAuction curAuction, AuctionAdapter.Winner winner) {
        if (!isCurAuctionMyAuction()) {
            // we only bought power if we weren't the seller...
            takeStageOverseer().takeProductIntermediaryCustomer().boughtProduct(curAuction.productAmount, winner.offer, curAuction.seller.fetchId());
        }
    }

    private class ResultsStageGuide {
        public void invoke() throws ProductIntermediaryRaiser {
            sendResultsEndMessage();
        }
    }
}
