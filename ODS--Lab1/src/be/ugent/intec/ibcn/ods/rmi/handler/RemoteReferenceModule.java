package be.ugent.intec.ibcn.ods.rmi.handler;

import java.util.UUID;

import be.ugent.intec.ibcn.ods.rmi.call.RemoteCall;
import be.ugent.intec.ibcn.ods.rmi.call.RemoteInstance;
import be.ugent.intec.ibcn.ods.rmi.call.RemoteReturn;
import be.ugent.intec.ibcn.ods.rmi.exception.ODSRMIException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

/**
 * A handler who knows a RemoteInstance and its local implementations. Used to
 * delegate calls to the correct implementation objects.
 *
 * Local implementation objects must register with methods
 * {@link be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule#registerGlobal registerGlobal}
 * and
 * {@link be.ugent.intec.ibcn.ods.rmi.handler.RemoteReferenceModule#exportObject exportObject}
 * to work remotely.
 *
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.RemoteInstance
 */
public class RemoteReferenceModule {

    //Class attribute to hold the references towards the exported objects.
    private Map<RemoteInstance, Object> rMap = new HashMap<>();

    /*
     * Wrapper to register a Singleton class object
     * */
    @SuppressWarnings("unchecked") //$NON-NLS-1$
    public void registerGlobal(Class cInterface, Object objImplementation) throws ODSRMIException {
        exportObject(cInterface, objImplementation, null);
    }

    /*
     * Wrapper to register an object of a given class
     * */
    public void exportObject(Class cInterface, Object exportedObject) throws ODSRMIException {
        UUID objUUID = java.util.UUID.randomUUID();
        String instanceId = objUUID.toString();

        exportObject(cInterface, exportedObject, instanceId);
    }

    /**
     * Actual implementation of the object registration procedure
     *
     * @param cInterface
     * @param objImplementation
     * @param instanceId
     * @throws ODSRMIException
     */
    //TODO:: Implement the registration procedure
    @SuppressWarnings("unchecked") //$NON-NLS-1$
    private void exportObject(Class cInterface, Object objImplementation, String instanceId) throws ODSRMIException {
        RemoteInstance rInstance = new RemoteInstance(instanceId, cInterface.getName());

        rMap.put(rInstance, objImplementation);
    }

    /**
     * Retrieves a remote reference of a given object
     *
     * @param obj
     * @return
     */
    //TODO:: Implement the retrieval procedure
    RemoteInstance getRemoteReference(Object obj) {

        // Loop through the keys
        for (RemoteInstance rInstance : rMap.keySet()) {

            // If the object matches: return the remote instance
            if (rInstance.equals(obj)) {
                return rInstance;
            }
        }

        // Nothing found?
        return null;
    }

    /**
     * This procedure analyses the incoming message and invokes the appropriate
     * procedure from the server-object's implementation.
     *
     * @param remoteCall
     * @return
     * @throws ODSRMIException
     * @throws SecurityException
     * @throws NoSuchMethodException
     * @throws IllegalArgumentException
     * @throws IllegalAccessException
     */
    public RemoteReturn dispatchCall(RemoteCall remoteCall) throws ODSRMIException, SecurityException, NoSuchMethodException, IllegalArgumentException, IllegalAccessException {

        Object rObject = rMap.get(remoteCall.getRemoteInstance());


        /*
         * We, sadly, only have the method ID and not the name, so we can't use
         * the .getClass().getMethod() approach. We have to loop manually through
         * the methods from the object and find an equal method id.
         */
        Method method = null;

        /*
         * This isn't as easy as it seems: for example, we get:
         *  java.lang.String test.common.TestService.sayHello(java.lang.String)
         * and we have to match
         * public java.lang.String test.server.TestServer.sayHello(java.lang.String)
         * 
         * Firstly, we both remove the unnessecary parts from both method names so 
         * we become 
         * test.common.TestService.sayHello(java.lang.String)
         * and
         * test.server.TestServer.sayHello(java.lang.String)
         * We then replace one of the strings with the information from 
         * rObject.getClass().getName() and 
         * remoteCall.getRemoteInstance().getClassName(). Now we can check for
         * equality.
         */
        String lastPartRemote = remoteCall.getmName().split(" ")[remoteCall.getmName().split(" ").length - 1];
        
        for (Method m : rObject.getClass().getMethods()) {
            String lastPartLocal = m.toString().split(" ")[m.toString().split(" ").length - 1];
           
            String replacedLastPartLocal = lastPartLocal.replace(rObject.getClass().getName(), remoteCall.getRemoteInstance().getClassName());
                        
            if (replacedLastPartLocal.equals(lastPartRemote)) {
                // We have found the method, let's break out of it!
                method = m;
                break;
            }
        }

        // No method found? Throw an exception! This should not happen though.
        if (method == null) {
            throw new NoSuchMethodException();
        } else {
            try {
                Object result = method.invoke(rObject, remoteCall.getArgs());

                // Send the return with the calling ID
                return new RemoteReturn(result, remoteCall.getMessageID(), false, null);

            } catch (Exception e) {
                // Did an exception happen? Throw it back, throw it back!
                return new RemoteReturn(null, remoteCall.getMessageID(), true, e);
            }
        }

    }

    public static Class[] typeFromObjects(Object[] objects) {
        Class[] argClasses = null;
        if (objects != null) {
            argClasses = new Class[objects.length];
            for (int n = 0; n < objects.length; n++) {
                Object obj = objects[n];
                argClasses[n++] = obj.getClass();
            }
        }
        return argClasses;
    }
}
