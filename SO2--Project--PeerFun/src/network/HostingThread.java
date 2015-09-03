package network;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

/*
 *  @author Dieter Decaestecker
 *  class : HostingThread
 */
public class HostingThread implements Runnable
{
    private final NetworkAdapter adapter;
    private ServerSocket serverSocket;
    
    public HostingThread(NetworkAdapter adapter, int port)
    {
        this.adapter = adapter;
        try 
        {
            this.serverSocket = new ServerSocket(port);
        } 
        catch (IOException ex) 
        {
            if(adapter.getNetworkListener()!=null)
            {
                adapter.getNetworkListener().receiveData("COULD NOT HOST","127.0.0.1",adapter.getVerifierString(),0);   
            }
            adapter.setIsHosting(false);
        }
    }

    @Override
    public void run() 
    {
        while(adapter.isHosting())
        {
            try 
            {
                Socket socket = serverSocket.accept();
                if(socket!=null)
                {
                    new Thread(new ListenToSocketThread(adapter,socket,true,"")).start();
                }
            } 
            catch (IOException ex) 
            {
                if(adapter.isHosting())
                {
                    //Something went wrong
                    if(adapter.getNetworkListener()!=null)
                    {
                        adapter.getNetworkListener().receiveData("COULD NOT HOST","127.0.0.1",adapter.getVerifierString(),NetworkAdapter.getSingleton().getPortBeingHostedOn());   
                        adapter.setIsHosting(false);
                    }
                }
            }
        }
        try 
        {
            if(serverSocket!=null && !serverSocket.isClosed())
            {
                serverSocket.close();   
            }
        } 
        catch (IOException ex) {}
    }
    public ServerSocket getServerSocket() 
    {
        return serverSocket;
    }
}
