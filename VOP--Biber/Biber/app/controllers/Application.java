package controllers;

import static play.data.Form.form;

import com.avaje.ebean.ExpressionList;
import models.*;
import play.Routes;
import play.data.Form;
import play.data.validation.Constraints.Email;
import play.data.validation.Constraints.Required;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import scala.Option;
import utils.Hash;
import utils.LangMessages;
import utils.Mail;
import views.html.common.activate;
import views.html.common.index;
import views.html.common.login;
import views.html.common.alreadyLoggedIn;
import views.html.common.registerAsHalfRegisteredPupil;

import java.awt.*;
import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.mail.EmailException;
import org.codehaus.jackson.node.ObjectNode;
import views.html.selectLanguage;

public class Application extends Controller {
    private static final boolean debug = true;

    /**
     * Checks if the current user is logged in.
     *
     * @return Returns true in case the user is logged in,
     *                 false otherwise.
     */
    public static boolean isLoggedIn() {
        return session("bebrasId") != null;
    }

    /**
     * Checks if the current user has set a language.
     *
     * @return Returns true if the current user has set a language,
     *         false otherwise.
     */
    public static boolean isLanguageSet() {
        return session("language") != null;
    }

    /**
     * @return Returns the language the current user has set,
     *         or null in case the user has not set any language
     *         yet.
     */
    public static Language getLanguage() {
        return Language.valueOf(session("language"));
    }

    /**
     * Sets the language for the application and current user
     *
     * @param l Language we want to set for the current user
     */
    public static void setLanguage(Language l) {
        setLanguage(l, true);
    }

    /**
     * Sets the language for the application and/or current user
     *
     * @param l                 Language we want to set for the current user
     *
     * @param updateCurrentUser Set to true in case we want to update the language
     *                          of the current user in the database, or false in
     *                          case we don't want to do that
     */
    public static void setLanguage(Language l, boolean updateCurrentUser) {
        if (updateCurrentUser && isLoggedIn()) {
            Person p = getCurrentlyLoggedInPerson();
            p.language = l;
            p.save();
        }

        session("language", l.name());
    }

    /**
     * Get the currently logged in person.
     * @return Currently logged in person or null when noone logged in (-> session(bebrasId) empty).
     */
    public static Person getCurrentlyLoggedInPerson() {
        return Person.getPerson(session().get("bebrasId"));
    }

    /**
     * Get the currently logged in pupil.
     * @return Currently logged in pupil or null if session empty or bebraisd not of pupil.
     */
    public static Pupil getCurrentlyLoggedInPupil() {
        return Pupil.getPupil(session().get("bebrasId"));
    }

    /**
     * Get the currently logged in pupil.
     * @return Currently logged in teacher or null if session empty or bebrasId not of teacher.
     */
    public static Teacher getCurrentlyLoggedInTeacher() {
        return Teacher.getTeacher(session().get("bebrasId"));
    }

    /**
     * Get the currently logged in pupil.
     * @return Currently logged in teacher or null if session empty or bebrasId not of organizer.
     */
    public static Organizer getCurrentlyLoggedInOrganizer() {
        return Organizer.getOrganizer(session().get("bebrasId"));
    }

    /**
     * Get the currently logged in pupil.
     * @return Currently logged in teacher or null if session empty or bebrasId not of admin.
     */
    public static Admin getCurrentlyLoggedInAdmin() {
        return Admin.getAdmin(session().get("bebrasId"));
    }



    public static Result index(Option<String> lang) {
        if (lang.isDefined()) {
            Language l = Language.valueOf(lang.get());

            if (l != null)
                setLanguage(l);

            String url = request().getHeader(REFERER);
            if (url != null)
                redirect(url);
        }
        if (isLoggedIn())    // Logged in => profile page
            return redirect(routes.ProfilesController.seeProfile());
        else if (!isLanguageSet())   // Language not set => set DUTCH
            setLanguage(Language.DUTCH);  
        return ok(index.render());
    }

    /**
     * @return redirect to login page
     *         TODO if already logged in, don't show the login fields and show error message!
     */
    public static Result login() {
        if(isLoggedIn()){
            String url = request().getHeader(REFERER);
            if (url != null)
                redirect(url);
            else{
                return redirect(routes.ProfilesController.seeProfile());
            }
        }
        return ok(login.render(form(Login.class)));
    }

    /**
     * @return redirect to the account activation page if allowed to come there
     */
    public static Result render_activate() {
        //Person tried to access 'activate' page without coming from login page
        //TODO: redirect to other page?
        if (session("activate_id") == null) {
            return forbidden();
        } else {
            return ok(activate.render(form(Activate.class)));
        }
    }

    /**
     * @return redirect to the account activation page
     */
    public static Result activate() {
        if (session("activate_id") == null) {
            //TODO: redirect to other page?
            return forbidden();
        }

        Form<Activate> activateForm = form(Activate.class).bindFromRequest();
        if (activateForm.hasErrors()) {
            return badRequest(activate.render(activateForm));
        } else {
            Person p = Person.getPerson(session("activate_id"));
            p.firstPassword = "";
            p.password = Hash.createPassword(activateForm.get().newPassword);
            p.save();
            session().clear();
            return redirect(
                    routes.Application.login()
            );
        }
    }

    /**
     * Authenticate user and determine his role. BebrasId and user role saved in session.
     *
     * @return badrequest if auth failed, redirect to activate if account not yet activated
     */

    public static Result authenticate() {
        Form<Login> loginForm = form(Login.class).bindFromRequest();
        if (loginForm.hasErrors()) {
            return badRequest(login.render(loginForm));
        } else {
            String bebrasId = loginForm.get().bebrasId;
            Person p = Person.getPerson(bebrasId);
            if(p.isOnline() && session("mimickId") == null) {
                return forbidden(alreadyLoggedIn.render(p));
            }
            //Person's account needs to be activate by choosing a password
            if (!p.firstPassword.equals("")) { // make empty or make null?
                session("activate_id", bebrasId);
                return redirect(routes.Application.render_activate());
            }
            session().clear();
            session("bebrasId", bebrasId);
            session("language", p.language.name());
            determineUserRole(p);

            p.timestamp = new Timestamp(System.currentTimeMillis());
            p.save();

            if (loginForm.get().returnUrl != "") {
                return redirect(loginForm.get().returnUrl);
            } else
                return redirect(routes.ProfilesController.seeProfile());
        }
    }

    /**
     * Given a Person object, the method determines the role of the user and sets the 'role' attribute in session accordingly
     */
    public static void determineUserRole(Person newUser) {
        if (newUser instanceof Teacher) {
            session("role", "teacher");
        }
        if (newUser instanceof Organizer) {
            session("role", "organizer");
        }
        if (newUser instanceof Pupil) {
            session("role", "pupil");
        }
        if (newUser instanceof Admin) {
            session("role", "admin");
        }
    }


    /**
     * Logs out the user by clearing all his session attributes. User gets redirected to login page
     * Log out message stored in flash-object to use by view of the redirect result.
     *
     * @return Returns Result, redirecting user to login page
     */
    public static Result logout() {
        Person p = getCurrentlyLoggedInPerson();
        if(p!= null){
            p.timestamp = null;
            p.save();
        }

        // We keep the previously selected language
        Language lang = getLanguage();
        session().clear();
        setLanguage(lang);

        flash("success", LangMessages.get("logout.success"));
        return redirect(
                routes.Application.login()
        );
    }

    public static Result renderRegisterAsHalfRegisteredPupil(){
        return ok(registerAsHalfRegisteredPupil.render(form(RegisterAsHalfRegisteredPupil.class)));
    }

    public static Result registerAsHalfRegisteredPupil(){
        Form<RegisterAsHalfRegisteredPupil> registerSinglePupilForm = Form.form(RegisterAsHalfRegisteredPupil.class).bindFromRequest();
        if (registerSinglePupilForm.hasErrors()) {
            return badRequest(registerAsHalfRegisteredPupil.render(registerSinglePupilForm));
        } else {
            Pupil pupil;
            String dateOfBirth = registerSinglePupilForm.get().dateOfBirth;
            int dayOfBirth = Integer.parseInt(dateOfBirth.substring(0, 2));
            int monthOfBirth = Integer.parseInt(dateOfBirth.substring(3, 5));
            int yearOfBirth = Integer.parseInt(dateOfBirth.substring(6, 10));
            pupil = Pupil.createPupil(
                    registerSinglePupilForm.get().email,
                    registerSinglePupilForm.get().firstName,
                    registerSinglePupilForm.get().lastName,
                    registerSinglePupilForm.get().gender,
                    registerSinglePupilForm.get().language, dayOfBirth,
                    monthOfBirth, yearOfBirth);
            try {
                Mail.sendMail(pupil.email, LangMessages.get("register.email.subject"), LangMessages.get("register.email.message", pupil.bebrasId,pupil.firstPassword));
                flash("success",LangMessages.get("register.checkMailForPassword"));
            } catch (EmailException e) {
                flash("important",LangMessages.get("register.error.mail",pupil.bebrasId,pupil.firstPassword));
                e.printStackTrace();
            }
            return redirect(routes.Application.login());
        }
    }

    /**
     * Ajax handler for mimicking a user.
     * @param bebrasIdToMimick
     * @return Json containing redirect link or status if mimick failed
     */
    public static Result mimickUser(String bebrasIdToMimick){ //TODO maybe cleanup role code!
        String currentRole = session().get("role");
        Person personToMimick = Person.getPerson(bebrasIdToMimick);
        ObjectNode result = Json.newObject();
        if (personToMimick == null) {
            session("role", currentRole); // reinstate former role
            result.put("status", LangMessages.get("mimickUser.error.notExisting"));
        } else {
            determineUserRole(personToMimick); // sets session attribute to role of new person
            if (canMimick(currentRole, session("role"))) {
                
                if(Person.getPerson(bebrasIdToMimick).isOnline()){
                    session("role", currentRole); // reinstate former role
                    result.put("status", LangMessages.get("mimickUsers.error.online"));
                }else{
                    session("mimickId", session("bebrasId")); // to later return as this person
                    session("mimickRole",currentRole);
                    session("bebrasId", bebrasIdToMimick);
                    result.put("redirect", routes.ProfilesController.seeProfile().url());
                }
            } else { // Role not high enough to mimick given person
                session("role", currentRole); // reinstate former role
                result.put("status", LangMessages.get("mimickUser.error.notAuthorized"));
            }
        }
        return ok(result);
    }

    public static Result stopMimick(){
        if(session("mimickId")==null){
            return badRequest(); //TODO better error handling
        }
        session("bebrasId",session("mimickId"));
        session("role",session("mimickRole"));
        session().remove("mimickId");
        session().remove("mimickRole");
        return redirect(routes.ProfilesController.seeProfile());
    }

    /**
     * Determines wether a person with a role can mimick the role with second parameter.
     * An admin can mimick everyone. An organizer can mimick a teacher. All the other possibilities aren't allowed
     * @param currentRole
     * @param roleToMimick
     * @return
     */
    private static boolean canMimick(String currentRole, String roleToMimick){
        if(currentRole.equals("admin"))
            return true;
        if(currentRole.equals("organizer") && roleToMimick.equals("teacher"))
            return true;
        return false;
    }

    /**
     * Private class defining the fields of the login form
     */

    public static class Login {

        @Required
        public String bebrasId;
        @Required
        public String password;
        public String returnUrl;

        public String validate() {
            if (Person.authenticate(bebrasId, password) == null) {
                flash("returnUrl",returnUrl);
                return LangMessages.get("login.invalidLogin");
            }
            return null;
        }
    }

    /**
     * Private class defining the fields of the activate account form
     */
    public static class Activate {

        @Required
        public String newPassword;
        @Required
        public String confirmNewPassword;

        /**
         * Defines rules for validation of the new password
         * TODO: Define other rules for own passwords?
         */
        public String validate() {
            //Checking if BebrasId exists is not necessary because this can only be reached from login page, where id is checked
            if (!newPassword.equals(confirmNewPassword)) {
                return LangMessages.get("activate.passwordsNotEqual");
            }
            return null;
        }

    }

    /**
     * Class defining form so that someone can register as a half-registered pupil.
     */
    public static class RegisterAsHalfRegisteredPupil{

        @Required
        public String firstName;
        @Required
        public String lastName;
        @Email
        @Required
        public String email;
        @Required
        public String gender;
        @Required
        public String language;
        @Required
        public String dateOfBirth;


        public String validate() {
            if(Person.findPersonByEmail(email) != null){
                return LangMessages.get("register.emailAlreadyInUse");
            }
            //http://www.mkyong.com/regular-expressions/how-to-validate-date-with-regular-expression/
            if(!dateOfBirth.matches("(0?[1-9]|[12][0-9]|3[01])/(0?[1-9]|1[012])/((19|20)\\d\\d)")){
                return LangMessages.get("registerSinglePupil.dateFormatNotCorrect");
            }
            return null;
        }

    }

    public static Result javascriptRoutes() {
        response().setContentType("text/javascript");
        return ok(
                Routes.javascriptRouter("jsRoutes",
                        routes.javascript.ProfilesController.renewOnline(),
                        routes.javascript.TeacherController.getPupilsStatus(),
                        routes.javascript.TeacherController.resetPupilPassword(),
                        routes.javascript.Application.mimickUser(),
                        routes.javascript.Competitions.openCompetition(),
                        routes.javascript.SetController.upgradeSet(),
                        routes.javascript.SetController.downgradeSet(),
                        routes.javascript.TeacherController.addClassToSchool(),
                        routes.javascript.TeacherController.addExistingPupilToClass(),
                        routes.javascript.MonitorCompetitionController.getPupilsStatusForCompetition(),
                        routes.javascript.QuestionsController.getQuestionInfo(),
                        routes.javascript.QuestionsController.setQuestionInfo(),
                        routes.javascript.SetController.editSet(),
                        routes.javascript.OrganizerController.getTeachersFromSchool(),
                        routes.javascript.MonitorFTPController.getStatus(),
                        routes.javascript.MergePupils.searchName(),
                        routes.javascript.Statistics.getStatsForQuestion(),
                        routes.javascript.QuestionsController.getQuestionContents(),
                        routes.javascript.QuestionsController.updateQuestion(),
                        routes.javascript.Statistics.showRightAndWrong()
                )

        );
    }

}
