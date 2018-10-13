package powerbroker_1.edu.networkcusp.buyOp;

import plv.colorado.edu.quantmchecker.qual.Summary;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsPublicIdentity;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;


/**
 * Data structure to hold all the information a seller needs to pick a winner:
 * Valid claims of winners, concessions of losers, and list of bidders who haven't yet submitted either
 * @author rborbely
 *
 */
public class BiddersStatus {

	public Map<ProtocolsPublicIdentity, Integer> claimedWinners; // users who have presented a valid claim as winner of the auction
	public Set<ProtocolsPublicIdentity> conceders; // users who have conceded this auction (informed us that they didn't win)
												  // Note: currently, only the seller receives concessions
	public Set<ProtocolsPublicIdentity> biddersNotReported; // users who bid on this auction but haven't yet provided a concession or valid win claim
	
	public BiddersStatus(){
		claimedWinners = new HashMap<ProtocolsPublicIdentity, Integer>();
		conceders = new TreeSet<ProtocolsPublicIdentity>();
		biddersNotReported = new TreeSet<ProtocolsPublicIdentity>();
	}
	
	public boolean verifyHighest(int claimedOffer){
		int highest=0;
		for (ProtocolsPublicIdentity customer : claimedWinners.keySet()){
			int offer = claimedWinners.get(customer);
			if (offer >highest){
				highest = offer;
			}
		}
		return claimedOffer ==highest;
	}

	@Summary({"this.biddersNotReported", "1"})
	public void addBidder(ProtocolsPublicIdentity customer){
		biddersNotReported.add(customer);
	}
	
	// remove bidder from biddersNotReported
	public void removeBidder(ProtocolsPublicIdentity customer){
		biddersNotReported.remove(customer);
	}

	@Summary({"this.conceders", "1"})
	public void addConcession(ProtocolsPublicIdentity customer){
		conceders.add(customer);
		removeBidder(customer);
	}

	@Summary({"this.claimedWinners", "1"})
	public void addWinClaim(ProtocolsPublicIdentity customer, int offer){
		claimedWinners.put(customer, offer);
		removeBidder(customer);
	}
	
	public String toString(){
		String result ="";
		result += "Bidders who claim to have won:\n";
		for (ProtocolsPublicIdentity customer : new TreeSet<>(claimedWinners.keySet())){ // treeset to make sure output is consistently ordered
			result += customer.fetchId() + ", with bid of $" + claimedWinners.get(customer) + "\n";
		}
		result += "Bidders who have conceded:\n";
		for (ProtocolsPublicIdentity customer : conceders){
			result += customer.fetchId() + "\n";
		}
		result += "Remaining bidders:\n";
		for (ProtocolsPublicIdentity customer : biddersNotReported){
			result += customer.fetchId() + "\n";
		}
		return result;
	}
}
