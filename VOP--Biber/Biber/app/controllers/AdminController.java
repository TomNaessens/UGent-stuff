package controllers;

import org.apache.commons.mail.EmailException;

import controllers.security.SecuredAdmin;
import models.Organizer;
import models.Person;
import models.Pupil;
import play.data.DynamicForm;
import play.data.Form;
import play.data.validation.Constraints.Required;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import utils.LangMessages;
import utils.Mail;
import views.html.admin.registerOrganizer;

@Security.Authenticated(SecuredAdmin.class)
public class AdminController extends Controller {

    /**
     * @return Result rendering the register organizer page.
     */
    public static Result render_register_organizer(){
        return ok(registerOrganizer.render(Form.form(RegisterOrganizer.class)));
    }
    
    /**
     * POST-handler for registering a new organizer.
     */
    public static Result register_organizer(){
        Form<RegisterOrganizer> registerOrganizerForm = Form.form(RegisterOrganizer.class).bindFromRequest();
        if (registerOrganizerForm.hasErrors()) {
            return badRequest(registerOrganizer.render(registerOrganizerForm));
        }
        else{
            Organizer org = Organizer.createOrganizer(registerOrganizerForm.get().email, registerOrganizerForm.get().firstName, 
                    registerOrganizerForm.get().lastName, registerOrganizerForm.get().gender, registerOrganizerForm.get().language);
            try {
                Mail.sendMail(org.email, LangMessages.get("register.email.subject"), LangMessages.get("register.email.message", org.bebrasId,org.firstPassword));
                flash("success",LangMessages.get("registerOrganizer.success"));
            } catch (EmailException e) { //should not happen when in production mode
                flash("important",LangMessages.get("register.error.mail", org.bebrasId,org.firstPassword));
                e.printStackTrace();
            }
            return redirect(routes.AdminController.render_register_organizer());
        }
    }
    
    
    /**
     * Defines a form for registering organizer
     */
    public static class RegisterOrganizer{
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
        
        /**
         * If validates return null, everything ok. When it returns a string, this is the error message passed to the form handler.
         * @return
         */
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


    
    
}
