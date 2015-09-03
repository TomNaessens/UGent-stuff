package be.ugent.intec.ibcn.ods.rmi.call;

/**
 * Class that holds method call information.
 *
 */
//TODO:: Complete the implementation of this class
public class RemoteCall implements IRemoteMessage {
    
    private Long messageID; // The unique ID to identify the messages
    private RemoteInstance rInstance; // Object
    private String mName; // Methodname
    private Object[] args; // Arguments

    public RemoteCall(Long messageID, RemoteInstance obj, String mName, Object[] args) {
        this.messageID = messageID;
        this.rInstance = obj;
        this.mName = mName;
        this.args = args;
    }

    public Long getMessageID() {
        return messageID;
    }

    public RemoteInstance getRemoteInstance() {
        return rInstance;
    }

    public String getmName() {
        return mName;
    }

    public Object[] getArgs() {
        return args;
    }

}
