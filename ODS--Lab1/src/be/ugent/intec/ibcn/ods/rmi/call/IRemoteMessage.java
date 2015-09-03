package be.ugent.intec.ibcn.ods.rmi.call;

import java.io.Serializable;

/**
 *
 * @author Groep 18
 */

// We extend serializable here as we have to send the RemoteCall and Returns over
// the wire
public interface IRemoteMessage extends Serializable {
    
}
