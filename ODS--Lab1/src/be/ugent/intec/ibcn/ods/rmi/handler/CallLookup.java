package be.ugent.intec.ibcn.ods.rmi.handler;

import java.net.Socket;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A common static way to access the Socket which started the Delegator Thread.
 * A very useful way to know who called the current Method.
 *
 * @see	be.ugent.intec.ibcn.ods.rmi.handler.CallHandler
 */
public class CallLookup {

    //TODO - Create a container object to store all Thread - CommunicationModule tuples
    
    // Create the tuplemap; this has to be threaded so we use a concurrenthashmap as 
    // described in http://stackoverflow.com/questions/2688629/is-a-hashmap-thread-safe-for-different-keys
    private static Map<Thread, CommunicationModule> tuples = new ConcurrentHashMap<>();

    /**
     * Get the current Socket for this call. Only works in the main thread call.
     *
     * @return Socket which started the Delegator Thread
     */
    public static Socket getCurrentSocket() {
        //TODO:: return the correct Socket.

        // Get the communicationmodule by getting the current thread from the tuplemap
        CommunicationModule handler = tuples.get(Thread.currentThread());
        return (handler == null ? null : handler.getSocket());
    }

    /**
     * Register a new CommunicationModule
     *
     * @param connectionHandler
     */
    static void handlingMe(CommunicationModule communicationModule) {
        
        // Put the current thread in the map.
        // This is threaded, so synchronize it!
        synchronized (tuples) {
            tuples.put(Thread.currentThread(), communicationModule);
        }
    }

    /**
     * Remove an existing CommunicationModule
     *
     */
    static void forgetMe() {
        //TODO:: remove the CommunicationModule from the container
        
        // Remove the current thread from the map
        // This is threaded, so synchronize it!
        synchronized (tuples) {
            tuples.remove(Thread.currentThread());
        }
    }
}
