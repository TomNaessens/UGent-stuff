package be.ugent.intec.ibcn.ods.rmi.exception;

/**
 * General ODSRMI exception
 *
 */
public class ODSRMIException extends Exception {

    private static final long serialVersionUID = 7324141364282347199L;

    public ODSRMIException() {
        super();
    }

    public ODSRMIException(String message, Throwable cause) {
        super(message, cause);
    }

    public ODSRMIException(String message) {
        super(message);
    }

    public ODSRMIException(Throwable cause) {
        super(cause);
    }
}
