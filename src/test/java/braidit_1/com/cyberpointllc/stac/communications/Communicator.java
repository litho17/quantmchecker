package braidit_1.com.cyberpointllc.stac.communications;


public interface Communicator {
	
	public void transmit(CommunicationsPublicEmpty dest, byte[] msg) throws CommunicationsException;
}
