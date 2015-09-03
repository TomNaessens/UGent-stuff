package network;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.Socket;
import java.util.ArrayList;

/*
 *  @author Dieter Decaestecker
 *  class : ListenToSocketThread
 */
public class ListenToSocketThread implements Runnable
{
    private final NetworkAdapter adapter;
    private Socket socket;
    private ObjectOutputStream oos;
    private ObjectInputStream ois;
    
    private boolean threadIsAlive;
    private boolean handShakeSuccess;
    
    private String verifierString;
    
    public ListenToSocketThread(NetworkAdapter adapter, Socket socket, boolean comesFromHostThread,String whoIsThis)
    {
        this.adapter = adapter;
        this.socket = socket;
        this.adapter.addSocketThread(this);
        this.threadIsAlive = false;
        this.handShakeSuccess = false;
        try 
        {
            this.oos = new ObjectOutputStream(socket.getOutputStream());
        } 
        catch (IOException ex) 
        {
            return;
        }
        try
        {
            ois = new ObjectInputStream(socket.getInputStream());
        }
        catch(IOException ex)
        {
            return;
        }
        
        // Warning, massive leaking in to the constructor follows.
        
        if(comesFromHostThread)
        {   // We need to read from the other thread and send a response ( handshake )
            try
            {
                String first = (String) ois.readObject();       // What we recieve from the connecting thread
                verifierString = first.split(" ")[1];
                String second = adapter.getVerifierString();    // What it needs to be
                if(second!=null && !second.equals(first.split(" ")[0]))       // IF second == null it means there is no need for a check, join in :D 
                {
                    oos.writeObject("NOTOK");    // You are wrong, so send something that does not equal OK so when you read it you will die 
                    oos.flush(); 
                    return; 
                }
                else
                {
                    oos.writeObject("OK");       // You are correct or do not need a password, you can join :)
                    oos.flush();
                }
            }
            catch(IOException e)
            {
                return;
            }
            catch(ClassNotFoundException eb)
            {
                return;
            }
        }
        else
        {   // We need to send to the hoster and look at the response ( handshake )
            try 
            {
                verifierString = whoIsThis;
                oos.writeObject(whoIsThis + " " + adapter.getVerifierString());  // Stuur zijn en eigen verifierString door
                oos.flush();
                String confirm = (String) ois.readObject();
                if(!confirm.startsWith("OK"))  
                {
                    return;
                }
            } 
            catch (IOException ex) 
            {
                return;
            }
            catch(ClassNotFoundException eb)
            {
                return;
            }
        }
    
        handShakeSuccess = true;
        threadIsAlive = true;
        if(adapter.getNetworkListener()!=null)
        {   // Somehow everything works.
            adapter.getNetworkListener().receiveData("JOINED: " + socket.getInetAddress().getHostAddress(),socket.getInetAddress().getHostAddress(),verifierString,socket.getPort());     
        }
    }
    @Override
    public void run() 
    {
        while(adapter.isHosting() && threadIsAlive)
        {
            Object networkInput;
            try 
            {
                if((networkInput = ois.readObject()) != null) 
                {
                    if(networkInput.getClass().getCanonicalName().equals("java.lang.String"))
                    {   // String
                        String result = (String) networkInput;
                        if(result.startsWith(NetworkAdapter.KILL_TOKEN))
                        {
                            threadIsAlive = false;
                        }
                        else if(adapter.getNetworkListener()!=null)
                        {
                            adapter.getNetworkListener().receiveData(result,socket.getInetAddress().getHostAddress(),verifierString,socket.getPort());
                        }
                    }
                    else if(networkInput.getClass().getCanonicalName().equals("network.FileContents"))
                    {   // File
                        FileContents file = (FileContents) networkInput;
                        if(adapter.getNetworkListener()!=null)
                        {
                            adapter.getNetworkListener().receiveFileContents(file);
                        }
                    }
                }
            } 
            catch (IOException ex) 
            {
                threadIsAlive = false;
            } 
            catch (ClassNotFoundException ex) 
            {
                threadIsAlive = false;
            }
        }
        if(adapter.getNetworkListener()!= null && handShakeSuccess)
        {
            adapter.getNetworkListener().receiveData("LEFT: " + socket.getInetAddress().getHostAddress(),socket.getInetAddress().getHostAddress(),verifierString, socket.getPort());   
        }
        closeConnection();
        try 
        {
            ois.close();
        } catch (IOException ex) {}
        try 
        {
            oos.close();
        } catch (IOException ex) {}
        try 
        {
            socket.close();
        } catch (IOException ex) {}
    }
    public Socket getSocket() 
    {
        return socket;
    }
    public void setThreadIsAlive(boolean threadIsAlive) 
    {
        this.threadIsAlive = threadIsAlive;
    }
    public ObjectOutputStream getOos() 
    {
        return oos;
    }

    public void closeConnection()
    {
        String ip = socket.getInetAddress().getHostAddress();
        if(socket!=null)
        {
            if(adapter.getIpOnSocketMap().get(ip)!=null)
            {
                ArrayList<ListenToSocketThread> threads = adapter.getIpOnSocketMap().get(ip);
                for(int i=0; i<threads.size(); i++)
                {
                    if(socket.equals(threads.get(i).getSocket()))
                    {
                        adapter.getIpOnSocketMap().get(ip).remove(i);   
                        if(adapter.getIpOnSocketMap().get(ip).isEmpty())
                        {
                            adapter.getIpOnSocketMap().remove(socket.getInetAddress().getHostAddress());
                        }
                        return;
                    }
                }
            }
        }
    }
    public String getVerifierString() 
    {
        return verifierString;
    }
}
