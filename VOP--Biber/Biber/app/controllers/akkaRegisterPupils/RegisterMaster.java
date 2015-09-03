package controllers.akkaRegisterPupils;

import java.util.ArrayList;
import java.util.List;

import play.Logger;

import akka.actor.ActorRef;
import akka.actor.Props;
import akka.actor.UntypedActor;

public class RegisterMaster extends UntypedActor{

    
    private int progress;
    private int errorsToSend = 0;
    private List<String> errors = new ArrayList<String>();
    
    @Override
    public void onReceive(Object message) throws Exception {
        //Controller asks master to start a new job
        if (message instanceof ConfigMessage) {
            ConfigMessage config = (ConfigMessage) message;
            //Need to spawn child actor here..
            ActorRef child = this.getContext().actorOf(new Props(RegisterChildWorker.class));
            //make the child thread do stuff
            child.tell(new ConfigMessage("doSomething!",config.getFilename(),config.getFile(),config.getSchoolAndId(),config.getTeacher()),getSelf());
            child.tell(akka.actor.PoisonPill.getInstance(),getSelf());//kill the child after the work is complete...
        } else if (message instanceof StatusUpdate) { //Receives statusupdate from child
            StatusUpdate status = ((StatusUpdate) message);
            progress = status.getProgress();
        }
        else if(message instanceof ErrorUpdate){ //Receives new error from child
            errors.add(((ErrorUpdate)message).getError());
            errorsToSend++;
        }
        else if (message instanceof StatusAndErrorMessage) { //Receives request from view to report current status and errors
            List<String> resultErrors = (errors.size() > 0 && errorsToSend >0)? errors.subList(errors.size()-errorsToSend, errors.size()): null;
            getSender().tell(new ResultMessage(progress,resultErrors),getSelf());
            errorsToSend = 0;
            if (progress == 100) {
                // kill this actor, we're done!
                this.getSelf().tell(akka.actor.PoisonPill.getInstance(),getSelf());
            }
        } else {
            System.out.println("unhandled message" + message.toString());
            unhandled(message);
        }

    }

}