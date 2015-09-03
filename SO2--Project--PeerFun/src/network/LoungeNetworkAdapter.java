package network;

/**
 *
 * @author Dieter Decaestecker
 */
public interface LoungeNetworkAdapter 
{
	public boolean sendSerializableObject(Object object, String IP, int port);
	public boolean sendChatMessage(String message, String ID, String IP, int port);
        
        public void startHosting(String verifierString);
        public void stopHosting();
        
        public void openConnection(String IP, String isThisX);
        public void closeConnection(String IP, int port);
}
