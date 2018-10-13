package simplevote_1.com.cyberpointllc.stac.senderReceivers;


public interface Communicator {
	
	public void transmit(ProtocolsPublicUnity dest, byte[] msg) throws ProtocolsBad;
}
