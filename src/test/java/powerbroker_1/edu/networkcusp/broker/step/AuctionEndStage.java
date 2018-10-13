package powerbroker_1.edu.networkcusp.broker.step;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.OfferConveyData;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsConnection;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsRaiser;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsPublicIdentity;
import powerbroker_1.edu.networkcusp.broker.PurchasePlan;
import powerbroker_1.edu.networkcusp.broker.MyAuction;
import powerbroker_1.edu.networkcusp.broker.ProductIntermediaryAuction;
import powerbroker_1.edu.networkcusp.broker.ProductIntermediaryRaiser;
import powerbroker_1.edu.networkcusp.broker.Powerbrokermsg;
import powerbroker_1.edu.networkcusp.broker.buyOp.AuctionAdapter;
import powerbroker_1.edu.networkcusp.logging.Logger;
import powerbroker_1.edu.networkcusp.logging.LoggerFactory;

import java.util.*;

public class AuctionEndStage extends AuctionBaseStage {
    private final Logger logger = LoggerFactory.pullLogger(getClass());
    private final AuctionAdapter auctionAdapter;
    private final PurchasePlan offerPlan;
    private final int myOffer;

    /**
     * @param auctions       the entire list of auctions that we'll be processing at some point.  For the purposes of this
     *                       phase (and most others) we're only every concerned with the first auction on this list. That's
     *                       the 'current' auction.
     * @param myAuctions     a list of auctions that I've started.
     * @param offerPlan        the bidding plan that indicates what we should try to do.
     * @param auctionAdapter used to help us manage the current auction and the auction library.
     * @param stageOverseer
     */
    public AuctionEndStage(List<ProductIntermediaryAuction> auctions, List<MyAuction> myAuctions, PurchasePlan offerPlan, AuctionAdapter auctionAdapter, int myOffer, StageOverseer stageOverseer) {
        super(auctions, myAuctions, stageOverseer);
        this.offerPlan = offerPlan;
        this.auctionAdapter = auctionAdapter;
        this.myOffer = myOffer;
    }

    @Override
    public void enterStage() throws ProductIntermediaryRaiser {
        super.enterStage();

        // are we the bidder?  if so, close the auction
        if (isCurAuctionMyAuction()) {
            try {
                auctionAdapter.closeAuction(getCurrentAuction().id);
            } catch (Exception e) {
                throw new ProductIntermediaryRaiser(e);
            }
        }
    }

    @Override
    public Stage handleMsg(ProtocolsConnection connection, Powerbrokermsg.BaseMessage msg) throws ProductIntermediaryRaiser {
        if (msg.getType() == Powerbrokermsg.BaseMessage.Type.AUCTION_DATA) {
            try {
                auctionAdapter.handle(connection.takeTheirIdentity(), msg.getAuctionData().toByteArray());
            } catch (@InvUnk("Extend library class") ProtocolsRaiser e) {
                throw new ProductIntermediaryRaiser(e);
            }

            if (isCurAuctionMyAuction()) {
                // we have to wait for all the claims
                if (!auctionAdapter.hasReceivedAllClaimsAndConcessions()) {
                    // we're still expecting more bids, we have to wait
                    logger.info("handleMsg: still waiting for claims and concessions");
                    return null;
                } else {

                    // ok, we've got all the claims and concessions, we can announce a winner...
                    logger.info("claims received: " + auctionAdapter.claimsReceived.size());

                    ProtocolsPublicIdentity winner_ = null;
                    int winningOffer = 0;
                    if (auctionAdapter.claimsReceived.size() == 0) {
                        // I guess I won
                        winner_ = takeStageOverseer().obtainMyPublicIdentity();
                        winningOffer = myOffer;
                    } else {
                        @Bound("auctionAdapter.claimsReceived") int i;
                        @Inv("= (- claimIds it) (- c91 c90)") SortedSet<ProtocolsPublicIdentity> claimIds = new TreeSet<>();
                        @Iter("<= it auctionAdapter.claimsReceived") Iterator<ProtocolsPublicIdentity> it = auctionAdapter.claimsReceived.keySet().iterator();
                        while (it.hasNext()) {
                            ProtocolsPublicIdentity protocolsPublicIdentity;
                            c90: protocolsPublicIdentity = it.next();
                            c91: claimIds.add(protocolsPublicIdentity);
                        }
                        winner_ = claimIds.last();
                        winningOffer = auctionAdapter.claimsReceived.get(winner_).pullOffer();
                    }

                    if (winner_ == null) {
                        return handleMsgHandler();
                    }

                    try {
                        if (winner_.equals(takeStageOverseer().obtainMyPublicIdentity())) {
                            logger.info("handleMsg: I won! bid: " + winningOffer + " announcing...");
                        } else {
                            logger.info("handleMsg: " + winner_.obtainTruncatedId() + " won. bid: " + winningOffer + " announcing...");
                        }
                        auctionAdapter.announceWinner(getCurrentAuction().id, winner_, winningOffer);
                    } catch (Exception e) {
                        throw new ProductIntermediaryRaiser(e);
                    }

                    // it may be time to start sending these finished messages
                    return handlePotentialEnd();
                }
            } else {
                // we have to wait for the winner announcement
                AuctionAdapter.Winner winner = auctionAdapter.takeWinner();
                if (winner == null) {
                    // we're still expecting more bids, we have to wait
                    return handleMsgHerder();
                } else {
                    if (winner.winnerId.equals(takeStageOverseer().takeIdentity().pullId())) {
                        logger.info("handleMsg: I won! bid: " + winner.offer);
                    } else {
                        String wid = winner.winnerId;
                        if (wid.length() > 25){
                            wid = wid.substring(0, 25) + "...";
                        }
                        logger.info("handleMsg: " + wid + " won. bid: " + winner.offer);
                    }

                    // it may be time to start sending these finished messages
                    return handlePotentialEnd();
                }
            }
        } else if (msg.getType() == Powerbrokermsg.BaseMessage.Type.AUCTION_END) {
            addFinalMessage(connection.takeTheirIdentity(), msg);

            return handlePotentialEnd();
        } else {
            logger.error("Invalid message type in AuctionEndPhase: " + msg.getType() + " from " +
                    connection.takeTheirIdentity().obtainTruncatedId());
            List<ProtocolsPublicIdentity> pullFinalMessageAssign = getPriorStage().pullFinalMessageAssign();
            for (int q = 0; q < pullFinalMessageAssign.size(); q++) {
                handleMsgExecutor(pullFinalMessageAssign, q);
            }
            return null;
        }
    }

    private void handleMsgExecutor(List<ProtocolsPublicIdentity> pullFinalMessageAssign, int q) {
        new AuctionEndStageExecutor(pullFinalMessageAssign, q).invoke();
    }

    private Stage handleMsgHerder() {
        logger.info("handleMsg: still waiting for claims and concessions");
        return null;
    }

    private Stage handleMsgHandler() throws ProductIntermediaryRaiser {
        throw new ProductIntermediaryRaiser("No winner found!");
    }

    private Stage handlePotentialEnd() throws ProductIntermediaryRaiser {
        if (isItMyTurnToSendMessages()) {
            sendAuctionEndMessage();
        }

        return shouldTransitionToNextStage();
    }

    private void sendAuctionEndMessage() throws ProductIntermediaryRaiser {
        Powerbrokermsg.BaseMessage baseMessage = Powerbrokermsg.BaseMessage.newBuilder()
                .setType(Powerbrokermsg.BaseMessage.Type.AUCTION_END)
                .build();

        sendFinalMessage(baseMessage.toByteArray());
    }

    @Override
    protected Stage nextStage() throws ProductIntermediaryRaiser {

        // let the user know the auction is over
        takeStageOverseer().takeProductIntermediaryCustomer().auctionEnded(getCurrentAuction().id, getCurrentAuction().productAmount);

        logger.info("Moving to results phase");

        return new ResultsStage(auctions, myAuctions, offerPlan, auctionAdapter, takeStageOverseer());
    }

    private class AuctionEndStageExecutor {
        private List<ProtocolsPublicIdentity> pullFinalMessageAssign;
        private int a;

        public AuctionEndStageExecutor(List<ProtocolsPublicIdentity> pullFinalMessageAssign, int a) {
            this.pullFinalMessageAssign = pullFinalMessageAssign;
            this.a = a;
        }

        public void invoke() {
            ProtocolsPublicIdentity sender = pullFinalMessageAssign.get(a);
            System.out.println("Got final message from: " + sender.obtainTruncatedId());
        }
    }
}
