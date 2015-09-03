package controllers;

import org.apache.commons.mail.EmailException;

import models.Person;
import models.Token;
import play.data.validation.Constraints.Email;
import play.data.validation.Constraints.Required;
import play.i18n.Messages;
import play.mvc.Controller;
import play.mvc.Result;
import utils.LangMessages;
import utils.Mail;
import views.html.*;
import play.data.Form;
public class Reset extends Controller {
    
    /**
     * Class defining a form for asking to reset a pupil.
     */
    public static class AskResetForm{
        @Email
        public String email;
        public String bebrasId;
        
        /**
         * @return null if everything ok. Error message when something wrong
         */
        public String validate(){
            if(email.equals("") && bebrasId.equals("")){
                return utils.LangMessages.get("resetPassword.askResetForm.empty");
            }
            Person p = Person.getPerson(bebrasId);
            if((!email.equals("") && Person.findPersonByEmail(email) == null) || (!bebrasId.equals("") && p == null))
                return utils.LangMessages.get("resetPassword.askResetForm.notCorrect");
            if(p!= null && (p.email == null || p.email.equals(""))){
                return utils.LangMessages.get("resetPassword.askResetForm.askTeacherForReset");
            }
            return null;
        } 
    }
    
    /**
     * Displays the page for requesting a password reset.
     * @return
     */
    public static Result renderAskReset(){
        return ok(askReset.render(Form.form(AskResetForm.class)));
    }
    
    /**
     * Post for the askReset page. Generates a token and mails it to the user.
     * @return askReset page (possibly showing errors)
     */
    public static Result askReset(){
        Form<AskResetForm> askForm = Form.form(AskResetForm.class).bindFromRequest();
        if (askForm.hasErrors()) {
            return badRequest(askReset.render(askForm));
        }
        Person person = null; //will eventually never be null
        if (!askForm.get().bebrasId.equals(""))
            person = Person.getPerson(askForm.get().bebrasId);
        else if (!askForm.get().email.equals(""))
            person = Person.findPersonByEmail(askForm.get().email);
        try {
            Token.sendMailContainingToken(person);
            flash("success",Messages.get("resetPassword.askResetForm.success"));
        } catch (EmailException e) {
            flash("important",Messages.get("reset.error.mail"));
            e.printStackTrace();
        }
        return ok(askReset.render(askForm));
    }
    
    /**
     * Form for choosing a new password after reset.
     */
    public static class ResetForm{
        @Required
        public String newPassword;
        @Required
        public String confirmNewPassword;

        /**
         * Defines rules for validation of the new password
         * TODO: Define other rules for own passwords?
         */
        public String validate() {
            if (!newPassword.equals(confirmNewPassword)) {
                return utils.LangMessages.get("activate.passwordsNotEqual");
            }
            return null;
        }
        
        
    }
    
    
    /**
     * Renders the page to choose a new password.
     * @param token
     * @return
     */
    public static Result renderResetPassword(String token){
        if (token == null) {
            //flash("error", utils.LangMessages.get("error.technical"));
            Form<AskResetForm> askForm = Form.form(AskResetForm.class);
            return badRequest(askReset.render(askForm));
        }

        Token resetToken = Token.findByToken(token);
        if (resetToken == null) {
            //flash("error", utils.LangMessages.get("error.technical"));
            Form<AskResetForm> askForm = Form.form(AskResetForm.class);
            return badRequest(askReset.render(askForm));
        }

        if (resetToken.isExpired()) {
            resetToken.delete();
            flash("error", utils.LangMessages.get("resetPassword.tokenExpired"));
            Form<AskResetForm> askForm = Form.form(AskResetForm.class);
            return badRequest(askReset.render(askForm));
        }

        Form<ResetForm> resetForm = Form.form(ResetForm.class);
        return ok(resetPassword.render(resetForm, token));
    }

    /**
     * Takes password from the form and changes the password of the user.
     * @param token
     * @return
     */
    public static Result resetPassword(String token){
        Form<ResetForm> resetForm = Form.form(ResetForm.class).bindFromRequest();

        if (resetForm.hasErrors()) {
            return badRequest(resetPassword.render(resetForm, token));
        }
        
        Token resetToken = Token.findByToken(token);
        if (resetToken == null) {
            flash("error", utils.LangMessages.get("resetPassword.error.technical"));
            return badRequest(resetPassword.render(resetForm, token));
        }
        
        if (resetToken.isExpired()) {
            resetToken.delete();
            flash("error", utils.LangMessages.get("resetPassword.tokenExpired"));
            Form<AskResetForm> askForm = Form.form(AskResetForm.class);
            return badRequest(askReset.render(askForm));
        }
        
        Person person = Person.getPerson(resetToken.bebrasId);
        if (person == null) {
            // display no detail (email unknown for example) to
            // avoid check email by foreigner
            flash("error", utils.LangMessages.get("error.technical"));
            Form<AskResetForm> askForm = Form.form(AskResetForm.class);
            return badRequest(askReset.render(askForm)); // or resetpassword form?
        }
        
        String password = resetForm.get().newPassword;
        person.changePassword(password);
        
        try {
            sendPasswordChanged(person);
            flash("success", utils.LangMessages.get("resetPassword.success"));
        } catch (EmailException e) {
            flash("important",LangMessages.get("reset.error.mail"));
            e.printStackTrace();
        }
        return redirect(routes.Application.login());
    }

    /**
     * Send mail telling the person his password is reset.
     * @param Person to send the email to.
     * @throws EmailException 
     */
    private static void sendPasswordChanged(Person person) throws EmailException {
        String subject = utils.LangMessages
                .get("resetPassword.mail.success.subject");
        String message = utils.LangMessages
                .get("resetPassword.mail.success.message");
        Mail.sendMail(person.email, subject, message);
    }
}
