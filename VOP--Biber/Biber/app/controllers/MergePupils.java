package controllers;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import javax.persistence.Entity;

import models.ParticipationHistory;
import models.Pupil;
import models.School;
import models.Class;
import org.codehaus.jackson.node.ObjectNode;

import com.avaje.ebean.Ebean;

import play.data.DynamicForm;
import play.data.Form;
import play.db.ebean.Model;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import utils.LangMessages;
import views.html.teacher.mergePupils;
import controllers.security.SecuredTeacher;

@Security.Authenticated(SecuredTeacher.class)
public class MergePupils extends Controller {
    
    /**
     * Ajax handler for searching pupils with given name in a given school
     * @param name, name of the desired pupils.
     * @param schoolId, id of the school
     * @return json containing search results.
     */
    public static Result searchName(String name, String schoolId){
        ObjectNode result = Json.newObject();
        String[] names = name.split(",");
        if(names.length != 2)
            result.put("error", LangMessages.get("mergePupils.error.format"));
        else{
            String lastName = name.split(",")[0].trim();
            String firstName = name.split(",")[1].trim();
            School school = School.findSchool(Long.parseLong(schoolId));
            List<DummyPupil> pupils = searchPupilsFromSchool(firstName, lastName, school);
            if(pupils.size()!=0){
                result.put("pupils", Json.toJson(pupils));
            }
        }
        return ok(result);
    }
    
    /**
     * @return result rendering the MergePupils page
     */
    public static Result renderMergePupils(){
        return ok(mergePupils.render(Application.getCurrentlyLoggedInTeacher().schools));
    }
    
    /**
     * POST Handler for merging pupils.
     * @return
     */
    public static Result mergePupils(){
        String[] selected = request().body().asFormUrlEncoded().get("selected")[0].split(",");
        String idToKeep = request().body().asFormUrlEncoded().get("keep")[0];
        List<Pupil> otherPupils = new ArrayList<Pupil>();
        for(int i=0 ;i<selected.length; i++){
            selected[i] = selected[i].replaceAll("\\[", "").replaceAll("\\]","").replaceAll("\"", "").trim(); //UGLY UGLY UGLY
            if(!selected[i].equals(idToKeep))
                otherPupils.add(Pupil.getPupil(selected[i]));
        }
        if(idToKeep.equals("")){
            idToKeep = otherPupils.get(0).bebrasId;
            otherPupils.remove(0);
        }
        Pupil pupilToKeep = Pupil.getPupil(idToKeep);
        mergePupils(otherPupils, pupilToKeep);
        ObjectNode result = Json.newObject();
        result.put("ok",LangMessages.get("mergePupils.success"));
        return ok(result);
    }
    
    /**
     * Merge pupils in database
     * @param otherPupils
     * @param pupilToKeep
     */
    private static void mergePupils(List<Pupil> otherPupils, Pupil pupilToKeep){
        List<ParticipationHistory> history = ParticipationHistory.getAllHistory(otherPupils);
        for(ParticipationHistory hist: history){
            hist.participant = pupilToKeep;
        }
        Ebean.save(history);
        for(Pupil p: otherPupils){
            p.deactivated = true;
            p.currentClass = null;
            p.previousClass = null;
            p.save();
        }
        
    }
    
    /**
     * Search pupils with given name in given school
     * @param firstName
     * @param lastName
     * @param school
     * @return List of DummyPupils with the given name from given school.
     */
    private static List<DummyPupil> searchPupilsFromSchool(String firstName, String lastName, School school){
        List<Class> classes = Class.findSchoolClasses(school.id);
        List<DummyPupil> pupils = new ArrayList<DummyPupil>(); 
        for(Class c : classes){
            List<Pupil> temp = Pupil.findPupilsFromClass(c);
            for(Pupil p: temp){
                if(p.firstName.equals(firstName) && p.lastName.equals(lastName)){ //other search algorithm possible
                    String previousClass ="";
                    String currentClass = "";
                    if(p.currentClass != null)
                        currentClass = p.currentClass.name;
                    if(p.previousClass != null)
                        previousClass = p.previousClass.name;
                    DummyPupil dummy = new DummyPupil(p.isOnline(),school.name, p.firstName, p.lastName, p.bebrasId, currentClass, previousClass, p.dateOfBirth.toString("d-M-y"));
                    pupils.add(dummy);
                }
            }
        }
        return pupils;
    }
    
    /**
     * Dummy pupil for returning to Json. Json won't be able to serialize a regular pupil.
     */
    @Entity
    public static class DummyPupil extends Model{
        
        public String firstName;
        public String lastName;
        public String bebrasId;
        public String currentClassName;
        public String previousClassName;
        public String dateOfBirth;
        public String school;
        public boolean isOnline;
        
        public DummyPupil(boolean isOnline, String school, String firstName,String lastName,String bebrasId,String currentClassName,String previousClassName,String dateOfBirth) {
            this.isOnline = isOnline;
            this.school = school;
            this.firstName = firstName;
            this.lastName = lastName;
            this.bebrasId = bebrasId;
            this.currentClassName = currentClassName;
            this.previousClassName = previousClassName;
            this.dateOfBirth = dateOfBirth;
        }
    }
}
