package controllers.akkaRegisterPupils;

public class StatusUpdate {

    private int progress;
    
    public StatusUpdate(int progress) {
        this.progress = progress;
    }
    
    public int getProgress() {
        return progress;
    }
    
}
