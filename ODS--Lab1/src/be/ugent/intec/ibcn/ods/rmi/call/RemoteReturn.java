package be.ugent.intec.ibcn.ods.rmi.call;

/**
 * Class that holds method return information.
 *
 */
//TODO:: Complete the implementation of this class
public class RemoteReturn implements IRemoteMessage {

    private Object returnedObject; // The returned object
    private Long messageID; // Identifiable message ID
    private Boolean errorThrown; // Was there an error?
    private Throwable exception; // The error itself

    public RemoteReturn(Object returnedObject, Long messageID, Boolean errorThrown, Throwable exception) {
        this.returnedObject = returnedObject;
        this.messageID = messageID;
        this.errorThrown = errorThrown;
        this.exception = exception;
    }

    public Object getReturnedObject() {
        return returnedObject;
    }
    
    public Long getMessageID() {
        return messageID;
    }

    public Boolean getErrorThrown() {
        return errorThrown;
    }

    public Throwable getException() {
        return exception;
    }
    
}
