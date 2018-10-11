package battleboats_1.com.cyberpointllc.stac.dialogs;


public interface Communicator {
	
	public void send(TalkersPublicEmpty dest, byte[] msg) throws TalkersDeviation;
}
