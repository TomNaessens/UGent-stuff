package network;

/**
 *
 * @author Dieter Decaestecker
 */
public interface NetworkListener 
{
        public void receiveFileContents(FileContents file);
	public void receiveData(String networkInput, String ipFrom, String identifier, int port);
	public void sendData(String message, String ip, int port);
}