package be.ugent.intec.ibcn.ods.rmi.handler.filter;

import be.ugent.intec.ibcn.ods.rmi.call.IRemoteMessage;

/**
 * Default protocol filter implementation. Only forwards the data.
 *
 * @see be.ugent.intec.ibcn.ods.rmi.filter.GZipFilter
 */
public class DefaultFilter implements IProtocolFilter {

    @Override
    public IRemoteMessage readObject(Object obj) {
        return (IRemoteMessage) obj;
    }

    @Override
    public Object prepareWrite(IRemoteMessage message) {
        return message;
    }
}
