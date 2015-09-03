package be.ugent.intec.ibcn.ods.rmi.handler;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.lang.reflect.Method;
import java.net.Socket;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import be.ugent.intec.ibcn.ods.rmi.call.IRemoteMessage;
import be.ugent.intec.ibcn.ods.rmi.call.RemoteCall;
import be.ugent.intec.ibcn.ods.rmi.call.RemoteInstance;
import be.ugent.intec.ibcn.ods.rmi.call.RemoteReturn;
import be.ugent.intec.ibcn.ods.rmi.exception.ODSRMIException;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.IProtocolFilter;

/**
 * A CommunicationModule is an object which can call remote methods, receive
 * remote calls and dispatch its results.
 *
 *
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.RemoteInstance
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.RemoteCall
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.RemoteReturn
 * @see	be.ugent.intec.ibcn.ods.rmi.net.Client
 * @see	be.ugent.intec.ibcn.ods.rmi.net.Server
 * @see	be.ugent.intec.ibcn.ods.rmi.filter.DefaultFilter
 */
public class CommunicationModule implements Runnable {

    public static CommunicationModule createConnectionHandler(Socket socket, RemoteReferenceModule remoteReferenceModule, IProtocolFilter filter) {
        CommunicationModule connectionHandler = new CommunicationModule(socket, remoteReferenceModule, filter);

        String threadName = String.format("ConnectionHandler (%s:%d)", socket.getInetAddress().getHostAddress(), socket.getPort()); //$NON-NLS-1$
        Thread connectionHandlerThread = new Thread(connectionHandler, threadName);
        connectionHandlerThread.setDaemon(true);
        connectionHandlerThread.start();

        return connectionHandler;
    }

    public static CommunicationModule createConnectionHandler(Socket socket, RemoteReferenceModule remoteReferenceModule, IProtocolFilter filter, IConnectionHandlerListener listener) {
        CommunicationModule connectionHandler = createConnectionHandler(socket, remoteReferenceModule, filter);
        connectionHandler.addConnectionHandlerListener(listener);
        return connectionHandler;
    }
    private RemoteReferenceModule remoteReferenceModule;
    private Socket socket;
    private ObjectOutputStream output;
    private Long callId = 0L;
    private IProtocolFilter filter;
    private List<IConnectionHandlerListener> listeners = new LinkedList<>();
    private Map<RemoteInstance, Object> remoteInstanceProxys = new HashMap<>();
    private List<RemoteReturn> remoteReturns = new LinkedList<>();

    public void addConnectionHandlerListener(IConnectionHandlerListener listener) {
        listeners.add(listener);
    }

    public void removeConnectionHandlerListener(IConnectionHandlerListener listener) {
        listeners.remove(listener);
    }

    private CommunicationModule(Socket socket, RemoteReferenceModule remoteReferenceModule, IProtocolFilter filter) {
        this.remoteReferenceModule = remoteReferenceModule;
        this.socket = socket;
        this.filter = filter;
    }

    @Override
    public void run() {
        ObjectInputStream input;

        try {
            input = new ObjectInputStream(socket.getInputStream());

            while (socket.isConnected()) {
                Object objFromStream = input.readObject();

                IRemoteMessage remoteMessage = filter.readObject(objFromStream);

                if (remoteMessage instanceof RemoteCall) {

                    final RemoteCall remoteCall = (RemoteCall) remoteMessage;

                    //TODO - 1:: Implement the server side proxy creation logic.
                    Object proxyFromRemoteInstance = getProxyFromRemoteInstance(remoteCall.getRemoteInstance());
                    // Hmm, we don't actually do anything with these proxies. Makes me feel a bit uneasy.
                    
                    Thread delegator = new Thread(new Runnable() {
                        @Override
                        public void run() {
                            CallLookup.handlingMe(CommunicationModule.this);

                            RemoteReturn remoteReturn;
                            try {
                                try {
                                remoteReturn = remoteReferenceModule.dispatchCall(remoteCall);
                                } catch (Exception e) {
                                    remoteReturn = new RemoteReturn(null, remoteCall.getMessageID(), Boolean.TRUE, e);
                                }
                                sendMessage(remoteReturn);
                            } catch (IOException e) {
                                System.err.println(e);
                            }

                            CallLookup.forgetMe();
                        }
                    }, "Delegator"); //$NON-NLS-1$
                    delegator.setDaemon(true);
                    delegator.start();
                } else if (remoteMessage instanceof RemoteReturn) {
                    //TODO - 2:: Implement the client side return value reception logic.

                    // We know we have a RemoteReturn message; so let's cast it.
                    RemoteReturn remoteReturn = (RemoteReturn) remoteMessage;

                    // We are threading, so be threadsafe!
                    synchronized (remoteReturns) {
                        remoteReturns.add(remoteReturn);
                        remoteReturns.notifyAll();
                    }

                } else {
                    throw new ODSRMIException("Unknown IRemoteMessage type"); //$NON-NLS-1$
                }
            }
        } catch (IOException | ClassNotFoundException | ODSRMIException e) {
            try {
                socket.close();
            } catch (IOException e1) {
            }

            //TODO - 3:: Implement measures to avoid deadlocks

            // Thread safety above all safety
            synchronized (remoteReturns) {
                remoteReturns.notifyAll();
            }

            for (IConnectionHandlerListener listener : listeners) {
                listener.connectionClosed();
            }
        }
    }

    private synchronized void sendMessage(IRemoteMessage remoteMessage) throws IOException {
        if (output == null) {
            output = new ObjectOutputStream(socket.getOutputStream());
        }

        Object objToWrite = filter.prepareWrite(remoteMessage);

        output.writeObject(objToWrite);
        output.flush();
    }

    final Object remoteInvocation(final Object proxy, final Method method, final Object[] args) throws Throwable {
        final Long id = callId++;

        RemoteInstance remoteInstance;
        remoteInstance = getRemoteInstanceFromProxy(proxy);
        if (remoteInstance == null) {
            remoteInstance = new RemoteInstance(null, proxy.getClass().getInterfaces()[0].getName());
        }

        if (args != null) {
            for (int n = 0; n < args.length; n++) {
                RemoteInstance remoteRef = remoteReferenceModule.getRemoteReference(args[n]);
                if (remoteRef != null) {
                    args[n] = remoteRef;
                }
            }
        }

        String methodId = method.toString().substring(15);
        // I don't understand the trouble of the toString().substring part. Why
        // don't we just pass the method.getName() and the argumentlisttypes?

        //TODO - 4:: Complete the remoteCall initialisation
        IRemoteMessage remoteCall = new RemoteCall(id, remoteInstance, methodId, args);
        sendMessage(remoteCall);

        RemoteReturn remoteReturn = null;
        boolean bReturned = false;

        //TODO - 5:: Implement the client side return value analysis, keeping in mind the multithreaded nature of the server implementation.

        /*
         * This is tricky: We want to check if we have received a messages back.
         * Therefore; as long as we are connected, we loop through our returned
         * list of messages. If we find an ID we are waiting for; we put the
         * returned flag on true. We then remove the returned message from our
         * waiting queue. If we found the message, we remote it from the waiting
         * queue.
         * We also have to wait or/and synchronise here for thread safety.
         */
        do {
            synchronized (remoteReturns) {
                for (RemoteReturn rReturn : remoteReturns) {
                    if (rReturn.getMessageID().equals(id)) {
                        bReturned = true;
                        remoteReturn = rReturn;
                        break;
                    }
                }
                if (bReturned) {
                    remoteReturns.remove(remoteReturn);
                } else {
                    try {
                        remoteReturns.wait();
                    } catch (InterruptedException ie) {
                    }
                }
            }
        } while (socket.isConnected() && !bReturned);

        if (!socket.isConnected() && !bReturned) {
            throw new ODSRMIException("Connection aborted"); //$NON-NLS-1$
        }
        
        // Do we have an error? Throw it!
        if(remoteReturn.getErrorThrown()) {
            System.err.println("Abort abort! We've encountered an error!");
            throw (Throwable) remoteReturn.getException();
        }

        // Finally, return the object the server gave us
        return remoteReturn.getReturnedObject();
    }

    private Object getProxyFromRemoteInstance(RemoteInstance remoteInstance) {
        Object proxy = remoteInstanceProxys.get(remoteInstance);
        if (proxy == null) {
            try {
                proxy = CallProxy.buildProxy(remoteInstance, this);
            } catch (ClassNotFoundException e) {
                System.err.println(e);
            }
            remoteInstanceProxys.put(remoteInstance, proxy);
        }
        return proxy;
    }

    private RemoteInstance getRemoteInstanceFromProxy(Object proxy) {
        for (RemoteInstance remoteInstance : remoteInstanceProxys.keySet()) {
            if (remoteInstanceProxys.get(remoteInstance) == proxy) {
                return remoteInstance;
            }
        }

        return null;
    }

    public Socket getSocket() {
        return socket;
    }
}
