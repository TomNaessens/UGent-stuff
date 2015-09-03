package controllers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.mail.EmailException;
import org.codehaus.jackson.node.ObjectNode;

import models.Person;
import models.Pupil;
import models.School;
import models.Teacher;
import play.data.DynamicForm;
import play.data.Form;
import play.data.validation.Constraints.Required;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import utils.LangMessages;
import utils.Mail;
import views.html.organizer.registerTeacher;
import controllers.security.SecuredOrganizer;
import views.html.organizer.*;

import views.html.organizer.endYear;
import views.html.organizer.endYearSuccess;
import views.html.organizer.teacherPage;

@Security.Authenticated(SecuredOrganizer.class)
public class OrganizerController extends Controller {

    /**
     * Form to give to the startNewYear view.
     */
    private static DynamicForm form = new DynamicForm();

    /**
     * Renders registerTeacher page
     * @return
     */
    public static Result renderRegisterTeacher(){
        return ok(registerTeacher.render(Form.form(RegisterTeacher.class),getListOfSchoolLabels()));
    }
    
    /**
     * Handler for registering a teacher.
     * @return Redirect to the same page for registering another teacher
     */
    public static Result registerTeacher(){
        Form<RegisterTeacher> registerTeacherForm = Form.form(RegisterTeacher.class).bindFromRequest();
        if (registerTeacherForm.hasErrors()) {
            return badRequest(registerTeacher.render(registerTeacherForm,getListOfSchoolLabels()));
        }
        else{
            if(Person.findPersonByEmail(registerTeacherForm.get().email) != null){
                flash("important",LangMessages.get("register.emailAlreadyInUse"));
                return badRequest(registerTeacher.render(registerTeacherForm,getListOfSchoolLabels()));
            }
            List<School> schools = new ArrayList<School>();
            if(registerTeacherForm.get().selectedSchools == null){
                flash("important",LangMessages.get("register.selectSchool"));
                return badRequest(registerTeacher.render(registerTeacherForm,getListOfSchoolLabels()));
            }
            for(String schoolLabel: registerTeacherForm.get().selectedSchools){
                int i = schoolLabel.indexOf('-');
                schools.add(School.findSchool(Long.parseLong(schoolLabel.substring(0, i - 1))));
            }
            Teacher t = Teacher.createTeacher(registerTeacherForm.get().email, registerTeacherForm.get().firstName, registerTeacherForm.get().lastName, registerTeacherForm.get().gender, registerTeacherForm.get().language,registerTeacherForm.get().telephone, schools);
            try {
                Mail.sendMail(t.email, LangMessages.get("register.email.subject"), LangMessages.get("register.email.message", t.bebrasId,t.firstPassword));
                flash("success",LangMessages.get("registerTeacher.success"));
            } catch (EmailException e) {
                flash("important",LangMessages.get("register.error.mail", t.bebrasId,t.firstPassword));
                e.printStackTrace();
            }
            return redirect(routes.OrganizerController.renderRegisterTeacher());
        }
    }
    
    /**
     * Render page for registering a new school
     * @return
     */
    public static Result renderRegisterSchool(){
        return ok(registerSchool.render(Form.form(SchoolForm.class)));    
    }
    
    /**
     * Handles registering a new school.
     * @return Redirect to same page containing flash success message.
     */
    public static Result registerSchool(){
        Form<SchoolForm> schoolForm = Form.form(SchoolForm.class).bindFromRequest();
        if(schoolForm.hasErrors()){
            return badRequest(registerSchool.render(schoolForm));            
        }
        School school = new School(schoolForm.get().name, schoolForm.get().city, schoolForm.get().country, schoolForm.get().street, schoolForm.get().zipCode, schoolForm.get().number);
        flash("success",LangMessages.get("registerSchool.success", school.name));
        return redirect(routes.OrganizerController.renderRegisterSchool());
    }
    
    /**
     * Get a list of strings containing the school labels for the registerTeacher view.
     * @return List of Strings with school labels
     */
    private static List<String> getListOfSchoolLabels(){
        ArrayList<String> schoolLabels = new ArrayList<String>();
        for (School s : School.find.all())
            schoolLabels.add(s.id + " - " + s.name);
        return schoolLabels;
    }
    
    /**
     * Ajax handler for returning list of teachers.
     * @param schoolId
     * @return Json containing list of teachers
     */
    public static Result getTeachersFromSchool(long schoolId){
        ObjectNode result = Json.newObject();
        List<Teacher> teachers = Teacher.getTeachersFromSchool(schoolId);
        for(Teacher t: teachers)
            t.firstPassword="";
        result.put("teachers",Json.toJson(teachers));
        return ok(result);
    }
    
    /**
     * Renders teacher page so that organizer can view details and add school(s).
     * @param bebrasId
     * @return
     */
    public static Result renderTeacherPage(String bebrasId){
        Teacher t = Teacher.getTeacher(bebrasId);
        List<models.Class> c = models.Class.findClassesByTeacher(t);
        return ok(teacherPage.render(t,c));  
    }
    
    /**
     * Handler for adding a new school to an existing teacher. Parameters contained in formdata.
     * @return
     */
    public static Result addSchoolToTeacher(){
        long schoolId = Long.parseLong(DynamicForm.form().bindFromRequest().get("school"));
        String bebrasId = DynamicForm.form().bindFromRequest().get("teacher");
        Teacher t =  Teacher.getTeacher(bebrasId);
        t.schools.add(School.findSchool(schoolId));
        t.save();
        return redirect(routes.OrganizerController.renderTeacherPage(bebrasId));
    }
    
    /**
     * Class defining a form for registering a new teacher
     */
    public static class RegisterTeacher{
        @Required
        public String firstName;
        @Required
        public String lastName;
        @Required
        public String gender;
        @Required
        public String language;
        @Required
        public String email;
        public String telephone;
        
        public List<String> selectedSchools;
        
        //If validates return null, everything ok. When it returns a string, this is the error message passed to the form handler.
        public String validate() {
            if(!Person.emailCorrect(email)){
                return LangMessages.get("registerPupils.emailNotCorrect",email);
            }
            if(Person.findPersonByEmail(email) != null){
                return LangMessages.get("register.emailAlreadyInUse");
            }
            return null;
        }
    }

    /**
     * View the start of new school year page
     */
    public static Result render_endYear(){
        return ok(endYear.render(form));
    }

    /**
     * Invoked when the new year is started
     */
    public static Result endYear(){
        /*Remove class from each student*/
        for(Pupil p: Pupil.findAll()){
            if(p.currentClass!=null){
                p.previousClass = p.currentClass;
                p.currentClass = null;
                p.save();
            }
        }
        return ok(endYearSuccess.render());
    }
    
    /**
     * Class defining a form for registering a new school
     */
    public static class SchoolForm{
        
        @Required
        public String name;
        @Required
        public String city;
        /**
         * A String because there exists zipCodes with letters in some countries
         */
        @Required
        public String zipCode;
        @Required
        public String country;
        @Required
        public String street;
        /**
         * A String because there exists 17b, 210a, etc..
         */
        @Required
        public String number;
        
    }
    
}
