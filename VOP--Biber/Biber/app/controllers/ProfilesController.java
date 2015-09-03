package controllers;

import controllers.Application.Login;
import controllers.Assets;
import models.*;
import models.Class;
import play.api.Play;
import play.api.mvc.AnyContent;
import play.api.mvc.Call;
import play.api.mvc.Action;
import play.api.mvc.Request;
import play.data.DynamicForm;
import play.data.Form;
import play.mvc.Controller;
import play.mvc.Http;
import play.mvc.Result;
import utils.LangMessages;
import views.html.admin.profileAdministrator;
import views.html.admin.helpPageAdmin;
import views.html.common.login;
import views.html.common.editProfile;
import views.html.organizer.profileOrganizer;
import views.html.organizer.helpPageOrganizer;
import views.html.pupil.history;
import views.html.pupil.profilePupil;
import views.html.pupil.helpPagePupil;
import views.html.teacher.classForTeacher;
import views.html.teacher.profileTeacher;
import views.html.teacher.helpPageTeacher;


import javax.swing.text.html.HTML;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;
import java.nio.file.Path;
import java.util.*;
import java.sql.Timestamp;

import static play.data.Form.form;

public class ProfilesController extends Controller{
    private static DynamicForm form = new DynamicForm();

    public static Result seeProfile(){
        String bebrasId = session().get("bebrasId");
        String role = session().get("role");

        //Not authorized when role or bebras not set
        if(role == null || bebrasId == null){
            return forbidden(login.render(form(Login.class)));
        }
        if(role.equals("admin")){
            Admin a =  Admin.getAdmin(bebrasId);
            return ok(profileAdministrator.render(a));
        }
        if(role.equals("organizer")){
            Organizer o =  Organizer.getOrganizer(bebrasId);
            
            //The first list given to the profileOrganizer view is the list of competitions who haven't been terminated yet
            List<Competition> notYetTerminatedCompetitions = new ArrayList<>();
            //these are made up of the not yet opened competitions
            notYetTerminatedCompetitions.addAll(Competition.findOfficialCompetition(Competition.NOTVISIBLE));
            //and the opened competitions
            notYetTerminatedCompetitions.addAll(Competition.findOfficialCompetition(Competition.VISIBLE));
            
            //The second list given to the profileOrganizer view is the list of closed offical competitions
            List<Competition> terminatedCompetitions = Competition.findOfficialCompetition(Competition.CLOSED);
            return ok(profileOrganizer.render(o,notYetTerminatedCompetitions,terminatedCompetitions));
        }
        if(role.equals("teacher")){
            Teacher t =  Teacher.getTeacher(bebrasId);
            List<Class> list = Class.findClassesByTeacher(t);
            java.util.Set<Competition> set = new TreeSet<>();
            
            //The list of competitions that haven't been close yet are the competitions who are open and haven't been opened yet
            for(Class c : list) {
            	set.addAll(c.getOpenCompetitions());
            	set.addAll(c.getClosedCompetitions());
            }
            List<Competition> list2 = new ArrayList<>(set);
            
            
            TreeSet<Competition> tempterminatedCompetitions = new TreeSet<>();
            List<Class_Competition> ccList = Class_Competition.find.where().eq("currentClass.teacher.bebrasId", bebrasId).findList();
            for(Class_Competition cc : ccList) {
            	tempterminatedCompetitions.add(cc.competition);
            }
            for(Class_Competition cc : ccList) {
            	if(cc.isOpen != Class_Competition.TERMINATED) {
            		tempterminatedCompetitions.remove(cc.competition);
            	}
            }
            List<Competition> terminatedCompetitions = new ArrayList<>(tempterminatedCompetitions);
            return ok(profileTeacher.render(list2, list, terminatedCompetitions, t));
        }
        if(role.equals("pupil")){
            Pupil p =  Pupil.getPupil(bebrasId);
            List<Competition> list = p.findOpenCompetitions();
            return ok(profilePupil.render(list, p));
        }
        //Something went wrong
        return badRequest();
    }

    public static Result seeHistory(){
        Pupil p =  Application.getCurrentlyLoggedInPupil();
        List<ParticipationHistory> list = ParticipationHistory.getHistoryFor(p);
        Iterator<ParticipationHistory> it = list.iterator();

        // Filter out any official competitions that are not yet closed,
        // as well as any other competitions that are not closed for that
        // specific class that shouldn't show results
        // as well as any unfinished competition
        while (it.hasNext()) {
            ParticipationHistory h = it.next();

            if (!h.isFinished()) {  // Filter unfinished competitions
                it.remove();
            } else {
                Competition c = h.competition;

                // Filter competitions so that class isn't closed yet
                Class_Competition cc = null;

                if (p.currentClass != null)
                    cc = Class_Competition.findClassCompetition(c.id, p.currentClass.id);

                if (cc != null && cc.isOpen == Class_Competition.OPEN
                        && !c.compType.showResultsWhenNotClosed()) {
                    it.remove();
                // Filter official competitions that are not yet closed
                } else if (c.compType == CompetitionType.OFFICIAL && c.isOpen != Competition.CLOSED) {
                    it.remove();
                }

            }
        }

        return ok(history.render(list));
    }

    public static Result viewClass(Long id){
        Class cl = Class.findClassById(id);
        List<Pupil> list = Pupil.findPupilsFromClass(cl);
        return ok(classForTeacher.render(list,cl));
    }

    public static Result editProfile(){
        Person p = Application.getCurrentlyLoggedInPerson();
        /*Put default values in view*/
        Map<String, String> map = new HashMap<>();
        map.put("First Name",p.firstName);
        map.put("Last Name", p.lastName);
        if (p.language!=null) {
            map.put("Language", p.language.toString());
        }
        if (p.email!=null) {
            map.put("E-mail", p.email);
        }
        if (p.gender!=null) {
            map.put("Gender", p.gender.toString().toLowerCase());
        }
        if (Application.getCurrentlyLoggedInTeacher()!=null) {
           map.put("telephone",((Teacher)p).telephone);
        }
        form = form.fill(map);
        return ok(editProfile.render(form, p));
    }

    public static Result submitChangesProfile(){
        Person p = Application.getCurrentlyLoggedInPerson();
        DynamicForm requestData = form.bindFromRequest();
        String firstName = requestData.get("First Name");
        String lastName = requestData.get("Last Name");
        String email = requestData.get("Email");
        String gender = requestData.get("Gender").toUpperCase();
        String language = requestData.get("Language").toUpperCase();
        if(email != "" && !Person.emailCorrect(email)){
            flash("important",LangMessages.get("editProfile.mailIncorrect", email));
            return redirect(routes.ProfilesController.editProfile());
        }
        if (lastName != "")
            p.lastName = lastName;
        if (firstName != "")
            p.firstName = firstName;
        if (email != "")
            p.email = email;
        if (gender != "")
            p.gender = Gender.valueOf(gender);
        if (language != "") {
            p.language = Language.valueOf(language);
            Application.setLanguage(p.language, false);    // Set application language as well
        }
        if(Application.getCurrentlyLoggedInTeacher()!=null){
            String tel = requestData.get("telephone") ;
            ((Teacher)p).telephone = tel;
        }
        p.save();
        return seeProfile();
    }


    public static Result renewOnline() {
        Person p = Application.getCurrentlyLoggedInPerson();
        if (p != null) {
            p.timestamp = new Timestamp(System.currentTimeMillis());
            p.save();
        }
        return ok();
    }

    public static Result downloadManual() {
        if(!Application.isLanguageSet()){
            Application.setLanguage(Language.ENGLISH);
        }
        String suffix = "";
        if (Language.DUTCH.equals(Application.getLanguage())) {
            suffix = "_nl.pdf";
        } else {
            suffix = "_en.pdf";
        }
        Person p = Application.getCurrentlyLoggedInPerson();
        /*Manual at homepage is the admin manual*/
        if (p == null) {
            return redirect(routes.Assets.at("manuals/manual_admin"+suffix));
        }
        /*Manuals when logged in is specific for type of user*/
        String name = p.getManualName()+suffix;
        return redirect(routes.Assets.at("manuals/" + name));
    }




    public static Result renderHelpPage() {
        Person p = Application.getCurrentlyLoggedInPupil();
        if (p!=null) {
            return ok(helpPagePupil.render());
        }
        p = Application.getCurrentlyLoggedInTeacher();
        if (p!=null) {
            return ok(helpPageTeacher.render());
        }
        p = Application.getCurrentlyLoggedInOrganizer();
        if (p!=null) {
           return ok(helpPageOrganizer.render());
        }
        p = Application.getCurrentlyLoggedInAdmin();
        if (p!=null) {
            return ok(helpPageAdmin.render());
        } else {
            return ok(helpPagePupil.render());
        }
    }
}
