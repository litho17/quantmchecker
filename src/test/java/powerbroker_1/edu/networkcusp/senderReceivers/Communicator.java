package powerbroker_1.edu.networkcusp.senderReceivers;


public interface Communicator {
	
	public void send(ProtocolsPublicIdentity dest, byte[] msg) throws ProtocolsRaiser;
}
