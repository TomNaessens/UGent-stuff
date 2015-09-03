package controllers;

import static akka.pattern.Patterns.ask;
import static play.data.Form.form;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import models.Class;
import models.Person;
import models.Pupil;
import models.School;
import models.Teacher;

import org.apache.commons.mail.EmailException;
import org.codehaus.jackson.node.JsonNodeFactory;
import org.codehaus.jackson.node.ObjectNode;
import org.joda.time.DateTime;

import play.Logger;
import play.data.DynamicForm;
import play.data.Form;
import play.data.validation.Constraints.Email;
import play.data.validation.Constraints.Required;
import play.libs.Akka;
import play.libs.F;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Http.MultipartFormData;
import play.mvc.Http.MultipartFormData.FilePart;
import play.mvc.Result;
import play.mvc.Security;
import utils.Hash;
import utils.LangMessages;
import utils.Mail;
import views.html.teacher.registerPupils;
import views.html.teacher.registerSinglePupil;
import akka.actor.ActorRef;
import akka.actor.Props;
import controllers.akkaRegisterPupils.ConfigMessage;
import controllers.akkaRegisterPupils.RegisterMaster;
import controllers.akkaRegisterPupils.ResultMessage;
import controllers.akkaRegisterPupils.StatusAndErrorMessage;
import controllers.security.SecuredTeacher;

@Security.Authenticated(SecuredTeacher.class)
public class TeacherController extends Controller {

    /**
     * Render the register pupils page for a teacher. Teacher shouldn't be null
     * because if bebrasId in session wasn't one of a teacher, he wouldn't be
     * able to reach this method.
     *
     * @return
     */
    public static Result renderRegisterPupils() {
        // getSchoolLabelsForTeacher method can only be reached when logged in,
        // so it should give the correct result to the form
        return ok(registerPupils.render(getSchoolLabelsForTeacher()));
    }
    
    /**
     * Action for the POST request of the registerpupils page. Gets the uploaded
     * file and the name of the school for which the teacher wants to upload
     * pupils. Scans the extension of the file to determine which parse method
     * to use.
     *
     * @return SRC:http://stackoverflow.com/questions/9452375/how-to-get-the-upload
     *         -file-with-other-inputs-in-play2
     */
    public static Result registerPupilsUploader(){
        MultipartFormData body = request().body().asMultipartFormData();
        FilePart pupilsFile = body.getFile("file");
        String schoolAndId = body.asFormUrlEncoded().get("school")[0];
        ObjectNode result = Json.newObject();
        if (pupilsFile != null) {
          File file = pupilsFile.getFile();
          ActorRef myActor = Akka.system().actorOf(new Props(RegisterMaster.class));
          myActor.tell(new ConfigMessage("GOGO", pupilsFile.getFilename(), file, schoolAndId, Application.getCurrentlyLoggedInTeacher()), myActor);
          result.put("actorId", myActor.path().name());
        }
        return ok(result);
    }
    
    /**
     * Ajax handler for retrieving progress and errors.
     * @param uuid
     * @return Result containing the progress of the uploading job.
     */
    public static Result retrieveProgress(String uuid)
    {
        uuid =  "akka://application/user/"+uuid;
        ActorRef myActor = Akka.system().actorFor(uuid);
        if(myActor.isTerminated())
        {
           flash("succes",LangMessages.get("registerPupils.success"));
           ObjectNode result = Json.newObject();
           result.put("completed","true");
           return ok(result);
        }
        else
        {
            return async(
                    Akka.asPromise(ask(myActor,new StatusAndErrorMessage(), 7000)).map(
                            new F.Function<Object,Result>() {
                                public Result apply(Object response) {
                                    if(response instanceof ResultMessage)
                                    {
                                        ResultMessage message = (ResultMessage) response;
                                        ObjectNode result = Json.newObject();
                                        result.put("progress", message.getProgress()+"%");
                                        if(message.getErrors() != null){
                                            result.put("errors",Json.toJson(message.getErrors()));
                                        }
                                        return ok(result);
                                    }
                                    return ok(response.toString()); //should not happen
                                }
                            }
                    )
            );

        }
    }
    
    /**
     * Renders the registerSinglePupil page for class with given classID.
     * @param classID
     * @return Shows the page for registering a single pupil with a class.
     */
    public static Result renderRegisterSinglePupil(Long classID){
        Class foundClass = Class.findClassById(classID);
        return ok(registerSinglePupil.render(form(RegisterSinglePupil.class), foundClass ));
    }
    
    /**
     * Registers a single pupil for the class with given classID.
     * @param classID
     * @return Result, redirecting the teacher to the class page.
     */
    public static Result registerSinglePupil(Long classID){
        Form<RegisterSinglePupil> registerSinglePupilForm = Form.form(RegisterSinglePupil.class).bindFromRequest();
        Class classForPupil = Class.findClassById(classID);
        if(!Class.findTeacherClasses(session("bebrasId")).contains(classForPupil)){
            return badRequest("Invalid class in url");
        }
        if (registerSinglePupilForm.hasErrors()) {
            return badRequest(registerSinglePupil.render(registerSinglePupilForm, classForPupil));
        }
        else{
            String dateOfBirth = registerSinglePupilForm.get().dateOfBirth;
            int dayOfBirth = Integer.parseInt(dateOfBirth.substring(0, 2));
            int monthOfBirth = Integer.parseInt(dateOfBirth.substring(3,5));
            int yearOfBirth = Integer.parseInt(dateOfBirth.substring(6,10));
            Pupil pupil;
            try {
                pupil = Pupil.createPupilAndAssignClass(
                        registerSinglePupilForm.get().email,
                        registerSinglePupilForm.get().firstName,
                        registerSinglePupilForm.get().lastName,
                        registerSinglePupilForm.get().gender,
                        registerSinglePupilForm.get().language, dayOfBirth,
                        monthOfBirth, yearOfBirth, classForPupil);
                
                if (registerSinglePupilForm.get().email != "") {
                    Mail.sendMail(pupil.email, LangMessages
                            .get("register.email.subject"), LangMessages.get(
                            "register.email.message", pupil.bebrasId,
                            pupil.firstPassword));
                }
                Mail.sendMail(Application.getCurrentlyLoggedInTeacher().email, LangMessages
                        .get("register.email.subject"), LangMessages.get(
                        "register.email.message", pupil.bebrasId,
                        pupil.firstPassword));
                pupil.save();
            } catch (Exception e) {
                // TODO Auto-generated catch block
                e.printStackTrace(); //should not happen
            }
            return redirect(routes.ProfilesController.viewClass(classID));
        }
    }
    
    /**
     * Ajax handler for resetting a pupil's password
     * @param pupilBebrasId
     * @return
     */
    public static Result resetPupilPassword(String pupilBebrasId){
        Pupil pupil = Pupil.getPupil(pupilBebrasId);
        Teacher teacher =Application.getCurrentlyLoggedInTeacher();
        //Reset password of pupil
        pupil.firstPassword = Pupil.generateRandomPassword(10);
        pupil.password = Hash.createPassword(pupil.firstPassword);       
        pupil.save();
        //Send mail containing the new login information to the teacher
        try {
            Mail.sendMail(teacher.email, LangMessages.get("resetPupilPassword.mail.subject"), LangMessages.get("resetPupilPassword.mail.message", pupil.bebrasId,pupil.firstPassword));
        } catch (EmailException e) {
            ObjectNode result = Json.newObject();
            result.put("error", LangMessages.get("reset.error.mail"));
            return ok(result);
        }
        return ok();
    }

    /**
     * Service which returns that status for all pupils in a given class in the following JSON Format:
     * {'pupils': {
     *    'bebrasId1': {'status': true}
     *    'bebrasId2': {'status': false}
     *  }
     * }
     *
     * @param classID   The id of the class for which we want the pupils' status
     * @return
     */
    public static Result getPupilsStatus(Long classID) {
        ObjectNode result = Json.newObject();
        ObjectNode pupilsNode = Json.newObject();
        result.put("pupils", pupilsNode);

        // Check if the teacher actually can get information for this class
        Teacher teacher = Application.getCurrentlyLoggedInTeacher();
        if (teacher == null)
            return forbidden();

        Class clazz = Class.findClassById(classID);
        if (!Class.findClassesByTeacher(teacher).contains(clazz))
            return forbidden();

        // Loop through all students in the class and collect their status
        List<Pupil> pupils = Pupil.findPupilsFromClass(clazz);
        for (Pupil pupil : pupils) {
            ObjectNode node = JsonNodeFactory.instance.objectNode();
            node.put(
                    "status",
                    JsonNodeFactory.instance.booleanNode(pupil.isOnline())
            );
            pupilsNode.put(pupil.bebrasId, node);
        }

        return ok(result);
    }
    
    /**
     * Ajax handler for adding a class with given name to a given school for the current year.
     * @param school
     * @param className
     * @return Json result containing the status
     */
    public static Result addClassToSchool(String school, String className, String level) {
        Teacher teacher = Application.getCurrentlyLoggedInTeacher();
        int i = school.indexOf('-');
        long schoolId = Long.parseLong(school.substring(0, i - 1));
        if(!teacher.schools.contains(School.findSchool(schoolId))){
            flash("error","technical error");
            return redirect(routes.Application.logout());
        }
        ObjectNode result = Json.newObject();
        List<Class> classesOfSchool = Class.findSchoolClasses(schoolId);
        int year = DateTime.now().getYear();
        if (DateTime.now().getMonthOfYear() < 9) // so when adding a class in january 2013, year should be 2012                                      
            year--;
        //Check if class already exists in school
        for (Class c : classesOfSchool) {
            if (c.name.equals(className) && c.beginYear == year) {
                result.put("status", "alreadyExists");
                return ok(result);
            }
        }
        //Class does not exist already
        Class c = Class.createClass(className, level, year, School.findSchool(schoolId), teacher);        
        result.put("classId", c.id);
        result.put("className", c.name);
        result.put("classSchool", c.school.toString());
        return ok(result);
    }
    
    /**
     * Ajax handler for adding an existing pupil with given bebrasId to a given class 
     * @param classId
     * @param bebrasId
     * @return Json result containing status 
     */
    public static Result addExistingPupilToClass(String classId, String bebrasId){
        Class classForPupil = Class.findClassById(Long.parseLong(classId));
        if(!Class.findTeacherClasses(session("bebrasId")).contains(classForPupil) || classForPupil == null){
            return badRequest("Invalid class in url");
        }
        ObjectNode result = Json.newObject();
        Pupil p = Pupil.findPupilByBebrasID(bebrasId);
        if(p != null){
            p.currentClass = classForPupil;
            p.save();
            result.put("redirect",routes.ProfilesController.viewClass(Long.parseLong(classId)).url());
        }
        else{
            result.put("status","notExisting");
        }
        return ok(result);
    }

    /**
     * Get school labels in the form of 'id - schoolname' for a given teacher.
     * ONLY TO BE USED IN THIS CLASS AND WHEN TEACHER LOGGED IN
     * 
     * @return List of labels of schools of given teacher for use in the
     *         register_pupils page
     */
    private static List<String> getSchoolLabelsForTeacher() {
        Teacher teacher = Application.getCurrentlyLoggedInTeacher();
        ArrayList<String> schoolLabels = new ArrayList<String>();
        for (School s : teacher.schools)
            schoolLabels.add(s.id + " - " + s.name);
        return schoolLabels;
    }
    
    /**
     * Ajax handler for changing a classname with the editable plugin.
     * @return
     */
    public static Result changeClassName(){
        String newClassName = DynamicForm.form().bindFromRequest().get("value");
        Long classId = Long.parseLong(DynamicForm.form().bindFromRequest().get("classId"));
        School school = Class.findClassById(classId).school;
        List<Class> classList = Class.findSchoolClasses(school.id);
        int year = DateTime.now().getYear();
        if (DateTime.now().getMonthOfYear() < 9) // so when adding a class in january 2013, year should be 2012                                      
            year--;
        for(Class c : classList){
            if(c.name.equals(newClassName) && c.beginYear == year ){
                return badRequest(LangMessages.get("changeClassName.error",c.teacher.bebrasId));
            }
        }
        Class c =  Class.findClassById(classId);
        c.name = newClassName;
        c.save();        
        return ok();
    }


    public static Result downloadExamples(Long id){
        if (id.longValue() == 1) {
            return redirect(routes.Assets.at("/examples/XLSexample.xls"));
        }
        if (id.longValue() == 2) {
            return redirect(routes.Assets.at("/examples/XLSXexample.xlsx"));
        }

        return redirect(routes.Assets.at("/examples/CSVexample.csv"));
    }
    
    /**
     * Class defining form for registering a single pupil to a class.
     */
    public static class RegisterSinglePupil{
        
        @Required
        public String firstName;
        @Required
        public String lastName;
        @Email
        public String email;
        @Required
        public String gender;
        @Required
        public String language;
        @Required
        public String dateOfBirth;
        
        
        public String validate() {
            if((!email.equals("")) && Person.findPersonByEmail(email) != null){
                return LangMessages.get("register.emailAlreadyInUse");
            }
            //http://www.mkyong.com/regular-expressions/how-to-validate-date-with-regular-expression/
            if(!dateOfBirth.matches("(0?[1-9]|[12][0-9]|3[01])/(0?[1-9]|1[012])/((19|20)\\d\\d)")){
                return LangMessages.get("registerSinglePupil.dateFormatNotCorrect");
            }
            return null;
        }
        
    }

}
