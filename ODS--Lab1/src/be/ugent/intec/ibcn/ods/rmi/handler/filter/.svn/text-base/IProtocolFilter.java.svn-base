package be.ugent.intec.ibcn.ods.rmi.handler.filter;

import be.ugent.intec.ibcn.ods.rmi.call.IRemoteMessage;

/**
 * An interface to define a protocol filter to intercept messages and make any
 * needed modifications (ie. encryption/compression).
 *
 */
public interface IProtocolFilter {

    IRemoteMessage readObject(Object obj);

    Object prepareWrite(IRemoteMessage message);
}
