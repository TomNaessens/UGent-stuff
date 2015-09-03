package be.ugent.intec.ibcn.ods.rmi.net;

import java.net.Socket;

/**
 * This listener can be used to monitor a Server. (ie. to know when it receives new
 * connections or closes it)
 *
 *
 * @see be.ugent.intec.ibcn.ods.rmi.net.Server
 */
public interface IServerListener {

    void clientConnected(Socket socket);

    void clientDisconnected(Socket socket);
}
