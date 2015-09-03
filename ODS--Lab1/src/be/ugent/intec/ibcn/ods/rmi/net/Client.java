package be.ugent.intec.ibcn.ods.rmi.net;

import java.io.IOException;
import java.lang.reflect.Proxy;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;

import be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule;
import be.ugent.intec.ibcn.ods.rmi.handler.CallProxy;
import be.ugent.intec.ibcn.ods.rmi.handler.CommunicationModule;
import be.ugent.intec.ibcn.ods.rmi.handler.IConnectionHandlerListener;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.DefaultFilter;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.IProtocolFilter;

/**
 * The ODSRMI client. Connects to an ODSRMI Server on an address:port and
 * creates local dynamic proxies to call remote methods through a simple
 * interface.
 *
 *
 * @see be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule
 * @see be.ugent.intec.ibcn.ods.rmi.net.Server
 */
public class Client {

    private Socket socket;
    private CommunicationModule connectionHandler;
    private final IConnectionHandlerListener connectionHandlerListener = new IConnectionHandlerListener() {
        @Override
        public void connectionClosed() {
            for (IClientListener listener : listeners) {
                listener.disconnected();
            }
        }
    };
    private List<IClientListener> listeners = new LinkedList<>();

    public void addClientListener(IClientListener listener) {
        listeners.add(listener);
    }

    public void removeClientListener(IClientListener listener) {
        listeners.remove(listener);
    }

    public Client(String address, int port, RemoteReferenceModule callHandler) throws IOException {
        this(address, port, callHandler, new DefaultFilter());
    }

    public Client(String address, int port, RemoteReferenceModule callHandler, IProtocolFilter filter) throws IOException {
        socket = new Socket(address, port);
        connectionHandler = CommunicationModule.createConnectionHandler(socket, callHandler, filter, connectionHandlerListener);
    }

    public void close() throws IOException {
        socket.close();
    }

    public Object getGlobal(Class clazz) {
        return Proxy.newProxyInstance(clazz.getClassLoader(), new Class[]{clazz}, new CallProxy(connectionHandler));
    }
}
