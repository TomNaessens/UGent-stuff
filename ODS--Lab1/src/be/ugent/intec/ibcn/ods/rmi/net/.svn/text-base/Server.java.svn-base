package be.ugent.intec.ibcn.ods.rmi.net;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;

import be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule;
import be.ugent.intec.ibcn.ods.rmi.handler.CommunicationModule;
import be.ugent.intec.ibcn.ods.rmi.handler.IConnectionHandlerListener;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.DefaultFilter;
import be.ugent.intec.ibcn.ods.rmi.handler.filter.IProtocolFilter;

/**
 * The ODSRMI server. This object listens to a specific port and when a client
 * connects, it delegates the connection to a
 * {@link be.ugent.intec.ibcn.ods.rmi.handler.CommunicationModule CommunicationModule}.
 *
 *
 * @see be.ugent.intec.ibcn.ods.rmi.net.RemoteReferenceModule
 * @see be.ugent.intec.ibcn.ods.rmi.net.Client
 */
public class Server {

    private ServerSocket serverSocket;
    private boolean enabled;
    private List<IServerListener> listeners = new LinkedList<>();

    public void addServerListener(IServerListener listener) {
        listeners.add(listener);
    }

    public void removeServerListener(IServerListener listener) {
        listeners.remove(listener);
    }

    public void close() {
        enabled = false;
    }

    public void bind(int port, RemoteReferenceModule callHandler) throws IOException {
        bind(port, callHandler, new DefaultFilter());
    }

    public void bind(final int port, final RemoteReferenceModule callHandler, final IProtocolFilter filter) throws IOException {
        serverSocket = new ServerSocket();
        serverSocket.setPerformancePreferences(1, 0, 2);
        enabled = true;

        serverSocket.bind(new InetSocketAddress(port));

        Thread bindThread; //$NON-NLS-1$ //$NON-NLS-2$
        bindThread = new Thread(new Runnable() {
            @Override
            public void run() {
                while (enabled) {
                    Socket acceptSocket;
                    try {
                        acceptSocket = serverSocket.accept();

                        final Socket clientSocket = acceptSocket;
                        CommunicationModule.createConnectionHandler(clientSocket,
                                callHandler,
                                filter,
                                new IConnectionHandlerListener() {
                            @Override
                            public void connectionClosed() {
                                for (IServerListener listener : listeners) {
                                    listener.clientDisconnected(clientSocket);
                                }
                            }
                        });
                        for (IServerListener listener : listeners) {
                            listener.clientConnected(clientSocket);
                        }
                    } catch (IOException e) {
                        System.err.println(e);
                    }
                }
            }
        }, String.format("Bind (%d)", port));
        bindThread.start();
    }
}
