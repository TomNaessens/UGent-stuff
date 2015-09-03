package be.ugent.intec.ibcn.ods.rmi.handler;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;

import be.ugent.intec.ibcn.ods.rmi.call.RemoteInstance;

/**
 * A dynamic proxy which delegates interface calls to a CommunicationModule
 *
 *
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.CommunicationModule
 */
public class CallProxy implements InvocationHandler {

    private CommunicationModule communicationModule;

    public CallProxy(CommunicationModule communicationModule) {
        this.communicationModule = communicationModule;
    }

    @Override
    /**
     * Invokes a method on a given proxy object.
     * TODO:: Implement this method.
     */
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        // The client should silently pass the invocation to the remote server trough
        // the communicationmodule, so let's do this!
        return communicationModule.remoteInvocation(proxy, method, args);
    }

    public static Object buildProxy(RemoteInstance remoteInstance, CommunicationModule communicationModule) throws ClassNotFoundException {
        Class clazz = Class.forName(remoteInstance.getClassName());
        return Proxy.newProxyInstance(clazz.getClassLoader(), new Class[]{clazz}, new CallProxy(communicationModule));
    }
}