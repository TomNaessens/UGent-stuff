package test.server;

import be.ugent.intec.ibcn.ods.rmi.exception.ODSRMIException;
import be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.GZipFilter;
import be.ugent.intec.ibcn.ods.rmi.net.IServerListener;
import be.ugent.intec.ibcn.ods.rmi.net.Server;
import java.io.IOException;
import java.net.Socket;
import java.util.Random;


import test.common.Counter;
import test.common.TestService;

public class TestServer implements TestService {

    RemoteReferenceModule remoteReferenceModule;

    public TestServer() {
        System.out.println("Creating Server");
        Server server = new Server();
        System.out.println("Creating Remote Reference Module");
        remoteReferenceModule = new RemoteReferenceModule();
        try {
            System.out.println("Registrating implementation");
            remoteReferenceModule.registerGlobal(TestService.class, this);
            System.out.println("Binding");
            server.addServerListener(new IServerListener() {
                @Override
                public void clientConnected(Socket socket) {
                    System.out.println("Client connected: " + socket.getInetAddress());
                }

                @Override
                public void clientDisconnected(Socket socket) {
                    System.out.println("Client disconnected: " + socket.getInetAddress());
                }
            });
            server.bind(1234, remoteReferenceModule, new GZipFilter());
            System.out.println("Server listening");
        } catch (ODSRMIException | IOException e) {
        }

    }

    //TODO::
    //Implement this procedure which return a unique Counter object
    @Override
    public Counter getCounter() {
        // Create a new counter with a random number
        Counter counter = new CounterImpl(new Random().nextInt(1000));
        
        // Try to register it with the server
        try {
            remoteReferenceModule.exportObject(Counter.class, counter);
            
        } catch (ODSRMIException e) {
            System.err.println(e);
        }
        
        // Return the registered counter
        return counter;
    }

    //TODO::
    //Implement this procedure which return thr appropriate welcome message
    @Override
    public String sayHello(String name) {
        // There's no need to register this as an object; just return the String
        return name;
    }

    //TODO::
    //HomeWork - Implement this procedure to make the server throw an exception
    @Override
    public Throwable throwAnExceptionPlease() {
        
        // Let's do something stupid and force an exeption
        Counter counter2 = null;
        counter2.getNumber();
        
        return new Throwable();
    }
    
    
    public static void main(String[] args) {
        TestServer testServer = new TestServer();
    }
}
