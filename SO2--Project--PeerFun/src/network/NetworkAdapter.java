package network;

import java.io.File;
import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.SocketAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/*
 *  @author Dieter Decaestecker
 *  class : NetworkAdapter
 * 
 */

/*
 * Networking class. 
 * 
 * Call startHosting(verifierString) before you make connections, or nothing will happen.
 * Join others with openConnection(IP,verifierString)
 * When joining, the host will look if the verifierString you gave that host at the startHosting() method is the same as the one you 
 * gave to the connector at openConnection. If so, the connection will be succesful. If not, the connection will die.
 * 
 * startHosting  will try to host on a port from PORTSTANDARD to PORTSTANDARD+PORTMAXINTERVAL
 * The openConnection method will try to connect from PORTSTANDARD to PORSTANDARD+PORTMAXINTERVAL
 * As such, it is viable to work with 2 applications that both use the networkadapter.
 * 
 * Constructors are public but are not supposed to be used, unfortunately it is like that for testing purposes.
 */
public class NetworkAdapter implements LoungeNetworkAdapter
{
    private final Map<String,ArrayList<ListenToSocketThread>> ipOnSocketMap;
    
    private HostingThread hostThread;
    private NetworkListener networkListener;
    private boolean isHosting;
    private int portBeingHostedOn;
    
    private static NetworkAdapter SINGLETON;
    
    public static final String CHAT_TOKEN = "/c";
    public static final String KILL_TOKEN = "/d";
    
    public static final int PORTSTANDARD = 55537;
    
    public static final int PORTMAXINTERVAL = 4;
    
    private String verifierString;
    
    public NetworkAdapter(NetworkListener networkListener)
    {
        this.ipOnSocketMap = new HashMap<String,ArrayList<ListenToSocketThread>>();
        this.networkListener = networkListener;
        this.isHosting = false;
        this.hostThread = null;
        this.portBeingHostedOn = 0;
        this.verifierString = null;
    }
    public NetworkAdapter()
    {
        this.ipOnSocketMap = new HashMap<String,ArrayList<ListenToSocketThread>>();
        this.networkListener = null;
        this.isHosting = false;
        this.hostThread = null;
        this.portBeingHostedOn = 0;
        this.verifierString = null;
    }
    
    /***********************************/
    // Initialises the adapter.
    // String verifierString is the String that will be checked to the first message sent when making a connection 
    // that does not come from the HostThread.
    public void startHosting(String verifierString)
    {
        if(!isHosting)
        {
            this.verifierString = verifierString;
            for(int i=0; i<PORTMAXINTERVAL; i++)
            {
                isHosting = true;
                this.hostThread = new HostingThread(this, PORTSTANDARD+i);
                if(isHosting)   // Constructor changes boolean if it could not host on that port
                {
                    portBeingHostedOn = PORTSTANDARD+i;
                    new Thread(hostThread).start(); 
                    return;
                }
            }
            if(getNetworkListener()!=null)
            {
                getNetworkListener().receiveData("COULD NOT HOST","127.0.0.1",verifierString,portBeingHostedOn);   
            }
        }
    }
    // Does the same as above but allows  you to choose the port
    public void startHosting(String verifierString,int port)
    {   
        if(!isHosting)
        {
            this.verifierString = verifierString;
            isHosting = true;
            portBeingHostedOn = port;
            hostThread = new HostingThread(this, port);
            new Thread(hostThread).start();   
        } 
    }
    /***********************************/
    
    /***********************************/
    // Stop hosting, clean everything
    public void stopHosting()
    {
        if(isHosting)
        {
            portBeingHostedOn = 0;
            isHosting = false;
            for(String IP : ipOnSocketMap.keySet())
            {
                ArrayList<ListenToSocketThread> threads = ipOnSocketMap.get(IP);
                for(int i=0; i<threads.size(); i++)
                {
                    sendKillCommand(IP, threads.get(i).getSocket().getPort());   
                }
            }
            try 
            {
                if(hostThread!=null)
                {
                    hostThread.getServerSocket().close();   
                }
            } 
            catch (IOException ex) {}        
            hostThread = null;
            ipOnSocketMap.clear();    
        }
    }
    /***********************************/
    
    /***********************************/
    // Start listening to the Sockets and add them to the map ( is done in the thread )
    public void openConnection(String IP, String isThisX)
    {
        for(int i=0; i<PORTMAXINTERVAL; i++)
        {
            openConnection(IP,PORTSTANDARD+i,isThisX);  // Try to connect to everyone who is 'isThisX'
        }
    }
    private void openConnection(String IP, int port, String isThisX)
    {   
        if(IP.equals("127.0.0.1") && port == portBeingHostedOn)
        {
            // You are trying to connect to yourself, silly.
        }
        else if(isHosting)
        {
            Socket socket = null;
            try 
            {
                socket = new Socket();
		  SocketAddress socketAddress = new InetSocketAddress(IP, port); 
		  socket.connect(socketAddress, 3000); // 5 second timeout 
            } 
            catch (UnknownHostException ex) 
            { 
                return;
            } 
            catch (IOException ex) 
            { 
                return;
            }
            if(socket!=null)    
            {
                new Thread(new ListenToSocketThread(this,socket,false,isThisX)).start();
            }
        }
    }
    /***********************************/
    
    /***********************************/
    public void closeConnection(String IP, int port)
    {
        if(ipOnSocketMap.get(IP)!=null)
        {
            sendKillCommand(IP, port);
            ArrayList<ListenToSocketThread> threads = ipOnSocketMap.get(IP);
            for(int i=0; i<threads.size(); i++)
            {
                if(IP.equals(threads.get(i).getSocket().getInetAddress().getHostAddress()) && port == threads.get(i).getSocket().getPort())
                {
                    ipOnSocketMap.get(IP).get(i).setThreadIsAlive(false);
                    ipOnSocketMap.get(IP).remove(i);   
                    if(ipOnSocketMap.get(IP).isEmpty())
                    {
                        ipOnSocketMap.remove(IP);
                    }
                    return;
                }
            }
        }
    }
    public void closeConnection(String IP, String verifier)
    {
        if(ipOnSocketMap.get(IP)!=null)
        {
            sendKillCommand(IP,verifier);
            ListenToSocketThread thread = getSocketThreadWithIpAndVerifier(IP, verifier);
            thread.setThreadIsAlive(false);
            ipOnSocketMap.get(IP).remove(thread);   
            if(ipOnSocketMap.get(IP).isEmpty())
            {
                ipOnSocketMap.remove(IP);
            }
            return;
         }
    }
    /***********************************/
    
    /***********************************/
    // Getters, setters and adders
    public boolean isHosting() 
    {
        return isHosting;
    }
    public void setIsHosting(boolean isHosting) 
    {
        this.isHosting = isHosting;
    }
    public void addSocketThread(ListenToSocketThread thread)
    {
        if(ipOnSocketMap.get(thread.getSocket().getInetAddress().getHostAddress())==null)
        {
            ipOnSocketMap.put(thread.getSocket().getInetAddress().getHostAddress(),new ArrayList<ListenToSocketThread>());
        }
        ipOnSocketMap.get(thread.getSocket().getInetAddress().getHostAddress()).add(thread);
    }
    public Map<String, ArrayList<ListenToSocketThread>> getIpOnSocketMap()
    {
        return ipOnSocketMap;
    }
    public void setNetworkListener(NetworkListener networkListener) 
    {
        this.networkListener = networkListener;
    }
    public NetworkListener getNetworkListener() 
    {
        return networkListener;
    }
    public Set<String> getConnectedIPS()
    {
        return ipOnSocketMap.keySet();
    }
    public int getPortBeingHostedOn() 
    {
        return portBeingHostedOn;
    }
    public int amountOfPeopleOnThatIp(String IP)
    {
        return ipOnSocketMap.get(IP).size();
    }
    public ListenToSocketThread getSocketThreadWithPort(ArrayList<ListenToSocketThread> list, int port)
    {
        for(ListenToSocketThread thread : list)
        {
            if(thread.getSocket().getPort() == port)
            {
                return thread;
            }
        }
        return null;
    }
    public ListenToSocketThread getSocketThreadWithIpAndVerifier(String IP, String verifier)
    {
        ArrayList<ListenToSocketThread> list = ipOnSocketMap.get(IP);
        if(list==null) return null;
        else
        {
            for(ListenToSocketThread thread : list)
            {
                if(thread.getVerifierString().equals(verifier))
                {
                    return thread;
                }
            }
        }
        return null;
    }
    public String getVerifierString() 
    {
        return verifierString;
    }
    /***********************************/
    
    /***********************************/
    public boolean sendMessage(String message, String IP, String verifier)
    {
        try 
        {
            getSocketThreadWithIpAndVerifier(IP, verifier).getOos().writeObject(message);
            getSocketThreadWithIpAndVerifier(IP, verifier).getOos().flush();
        } 
        catch (IOException ex) 
        {
            return false;
        }
        catch(Exception e)
        {   // Gotta catch em all
            return false;
        }
        return true;
    }
    public boolean sendMessage(String message, String IP, int port)
    {
        try 
        {
            getSocketThreadWithPort(ipOnSocketMap.get(IP),port).getOos().writeObject(message);
            getSocketThreadWithPort(ipOnSocketMap.get(IP),port).getOos().flush();
        } 
        catch (NullPointerException npe)
        {
            return false;
        }
        catch(Exception e)
        {   // Gotta catch em all
            return false;
        }
        return true;
    }
    public boolean sendChatMessage(String message, String ID, String IP, int port)
    {
        return sendMessage(CHAT_TOKEN + " "  + ID + " " + message,IP, port);
    }
    public boolean sendChatMessage(String message, String ID, String IP, String verifier)
    {
        return sendMessage(CHAT_TOKEN + " "  + ID + " " + message,IP, verifier);
    }
    public void sendKillCommand(String IP, int port)
    {
        sendMessage(KILL_TOKEN,IP, port);
    }
    public void sendKillCommand(String IP, String verifier)
    {
        sendMessage(KILL_TOKEN,IP,verifier);
    }
    public boolean sendSerializableObject(Object object, String ip, int port)
    {
        try 
        {
            if(ipOnSocketMap.get(ip)!=null)
            {
                if(object.getClass().getCanonicalName().equals("java.io.File"))
                {
                    getSocketThreadWithPort(ipOnSocketMap.get(ip),port).getOos().writeObject(new FileContents((File)object));
                    getSocketThreadWithPort(ipOnSocketMap.get(ip),port).getOos().flush();
                }
                else
                {
                    getSocketThreadWithPort(ipOnSocketMap.get(ip),port).getOos().writeObject(object);
                    getSocketThreadWithPort(ipOnSocketMap.get(ip),port).getOos().flush();
                }
                return true;
            }
            return false;
        } 
        catch (IOException ex) 
        {
            return false;
        }
        catch(NullPointerException ex)
        {
            return false;
        }
    }
    public boolean sendSerializableObject(Object object, String ip, String verifier)
    {
        try 
        {
            if(ipOnSocketMap.get(ip)!=null)
            {
                if(object.getClass().getCanonicalName().equals("java.io.File"))
                {
                    getSocketThreadWithIpAndVerifier(ip,verifier).getOos().writeObject(new FileContents((File) object));
                    getSocketThreadWithIpAndVerifier(ip,verifier).getOos().flush();
                }
                else
                {
                    getSocketThreadWithIpAndVerifier(ip,verifier).getOos().writeObject(object);
                    getSocketThreadWithIpAndVerifier(ip,verifier).getOos().flush();
                }
                return true;
            }
            return false;
        } 
        catch (IOException ex) 
        {
            return false;
        }
        catch(NullPointerException ex)
        {
            return false;
        }
    }
    public static NetworkAdapter getSingleton()
    {
        if(SINGLETON==null)
        {
            SINGLETON = new NetworkAdapter();
        }
        return SINGLETON;
    }
    /***********************************/
}