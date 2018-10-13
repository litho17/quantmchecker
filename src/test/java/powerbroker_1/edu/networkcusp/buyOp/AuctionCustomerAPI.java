package powerbroker_1.edu.networkcusp.buyOp;

import powerbroker_1.edu.networkcusp.buyOp.messagedata.AuctionMessageData;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.PromiseData;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.ShareData;
import powerbroker_1.edu.networkcusp.buyOp.messagedata.OfferConveyData;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsPublicIdentity;

/**
 * Interface for users of the BidPal auction protocol.  
 * This is to communicate with the user (e.g. the bidder or seller), not for making the auction happen.
 * I.e., if you'd like to print a message to the screen or initiate some other action when a certain auction event occurs, 
 * this is the place to do it.  In some cases, it could easily be appropriate for these methods to do nothing at all. 
 * 
 * @author rborbely
 *
 */
public interface AuctionCustomerAPI {

	void newAuction(ProtocolsPublicIdentity customer, AuctionMessageData.AuctionStart data);
	void offerContractReceived(ProtocolsPublicIdentity customer, PromiseData data);
	void offerTestingReceived(ProtocolsPublicIdentity customer, ShareData data);
	void offerReceiptReceived(ProtocolsPublicIdentity customer, AuctionMessageData.OfferReceipt data);
	void biddingEnded(ProtocolsPublicIdentity customer, AuctionMessageData.BiddingOver data);
	void concessionReceived(ProtocolsPublicIdentity customer, AuctionMessageData.Concession data);
	void winClaimReceived(ProtocolsPublicIdentity customer, OfferConveyData data);
	void auctionOver(ProtocolsPublicIdentity customer, AuctionMessageData.AuctionEnd data);

}
