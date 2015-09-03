package controllers.akkaRegisterPupils;

/**
 * Message sent from child to master containing the latest found error.
 * @author Hannes
 *
 */
public class ErrorUpdate {

    private String error;
    
    public ErrorUpdate(String error) {
        this.error = error;
    }
    public String getError() {
        return error;
    }
    
}
