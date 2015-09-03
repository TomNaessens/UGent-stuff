package controllers.akkaRegisterPupils;

import java.util.List;

/**
 * Message sent from master to registerPupils view. Containing new errors and progress. Sent by master when view requests this.
 */
public class ResultMessage {

    private int progress;
    private List<String> errors;
    
    public ResultMessage(int progress, List<String> errors) {
        this.progress = progress;
        this.errors = errors;
    }
    
    public int getProgress() {
        return progress;
    }
    
    public List<String> getErrors() {
        return errors;
    }
}

