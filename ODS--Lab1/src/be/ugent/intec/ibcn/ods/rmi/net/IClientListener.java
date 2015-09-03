package be.ugent.intec.ibcn.ods.rmi.net;

/**
 * This listener can be used to monitor a Client. (ie. to know when it closed the
 * connection)
 *
 *
 * @see be.ugent.intec.ibcn.ods.rmi.net.Client
 */
public interface IClientListener {

    void disconnected();
}
