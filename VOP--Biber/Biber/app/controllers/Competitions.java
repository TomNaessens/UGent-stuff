package controllers;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import org.codehaus.jackson.JsonNode;
import org.codehaus.jackson.node.ObjectNode;
import org.springframework.context.support.ApplicationObjectSupport;

import models.Class;
import models.Class_Competition;
import models.Competition;
import models.CompetitionType;
import models.Competition_Language;
import models.Language;
import models.Level;
import models.Person;
import models.Set;
import models.Teacher;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import scala.collection.parallel.ParIterableLike.Find;
import views.html.createCompetition;
import views.html.anonymous.unrestrictedQuizzes;
import views.html.teacher.openCompetition;
import views.html.teacher.closeCompetition;

public class Competitions extends Controller {

	private static String[] ROLES = { "organizer", "teacher", "pupil" };
	private static CompetitionType[] TYPES = { CompetitionType.OFFICIAL,
			CompetitionType.LOCAL, CompetitionType.UNRESTRICTED };
	private static CompetitionAction[] ACTION = {
			new OrganizerCompetitionAction(), new TeacherCompetitionAction(),
			new PupilCompetitionAction() };

	/**
	 * 
	 * @param id
	 * @return
	 */
	public static Result render_open_competition(Long id) {
		Competition comp = Competition.findById(id);
		if (comp == null) {
			return notFound();
		}
		for (int i = 0; i < ROLES.length; i++) {
			if (session("role").equals(ROLES[i])) {
				return ACTION[i].renderOpenCompetition(comp);
			}

		}
		return redirect(routes.Application.login());
	}
	
	public static Result renderUnrestrictedCompetitions() {
	    if(!Application.isLanguageSet()){
            Application.setLanguage(Language.ENGLISH);
        }
		List<Competition> list = Competition.find.where().eq("compType",CompetitionType.UNRESTRICTED).eq("isOpen",Competition.VISIBLE).findList();
		return ok(unrestrictedQuizzes.render(list));
	}

	public static Result openCompetition(Long id) {
		Competition comp = Competition.find.where().eq("id", id).findUnique();
		Map<String, String[]> map = request().body().asFormUrlEncoded();
		for (int i = 0; i < ROLES.length; i++) {
			if (session("role").equals(ROLES[i])) {
				return ACTION[i].OpenCompetition(comp, map);
			}
		}
		return redirect(routes.Application.login());

	}

	public static Result render_create_competition() {
		List<Set> sets = null;
		int i;
		for (i = 0; i < ROLES.length; i++) {
			if (ROLES[i].equals(session("role"))) {

				return ACTION[i].renderCreateCompetiton();

			}
		}
		return Application.login();
	}

	public static Result createCompetition() {
		Map<String, String[]> map = request().body().asFormUrlEncoded();
		ArrayList<String> temp = new ArrayList<>();
		Map<Language, Competition_Language> titles = new TreeMap<Language, Competition_Language>();
		Set[] sets;
		Competition comp = null;
		for (Language l : Language.values()) {
			String title = map.get(l.name())[0];
			if (!title.equals("")) {
				Competition_Language compLang = new Competition_Language(
						title, l);
				titles.put(l, compLang);
			} 			
		}
		
		// Getting the chosen question sets 
		for (Level l : Level.values()) {
			try {
				String setID = map.get("Set"+l.name())[0];
				temp.add(setID);
			} catch(NullPointerException e) {}
		}
		boolean succes = true;
		// We can't create a competition without a name
		if (titles.keySet().isEmpty()) {
			flash("name", "false");
			succes = false;
		}
		// We can't allow competitions without question sets
		if ( temp.size() == 0 ) {
			flash("set", "false");
			succes = false;
		}
		
		// if there was a bug, we render the page again
		if (!succes) {
			return render_create_competition();
		}

		
		sets = new Set[temp.size()];
		int i;
		for (i = 0; i < sets.length; i++) {
			// getting the chosen sets
			sets[i] = Set.findById(Long.parseLong(temp.get(i)));
		}

		for (i = 0; i < ROLES.length; i++) {

			if (session("role").equals(ROLES[i])) {
				comp = Competition.createCompetition(titles, TYPES[i]);
				break;
			}
		}
		

		return ACTION[i].createCompetition(comp, sets);

	}

	public static Result renderCloseCompetition(Long id) {
		Competition comp = Competition.findById(id);
		if(comp == null) {
			return notFound();
		} else {
			for(int i = 0; i < ROLES.length; i++) {
				if(ROLES[i].equals(session("role"))) {
					return ACTION[i].renderCloseCompetition(comp);
				}
			}
		}
		return forbidden();
	}
	
	public static Result closeCompetition(Long id) {
		Competition comp = Competition.findById(id);
		Map<String,String[]> form = request().body().asFormUrlEncoded();
		for(int i = 0; i < ROLES.length; i++) {
			if(ROLES[i].equals(session("role"))) {
				return ACTION[i].closeCompetition(comp,form);
			}
		}
		return ok();
	}
	/**********************************************************************
	 * \
	 * 
	 * IMPLEMENT COMPETITION ACTIONS HERE
	 * 
	 * \
	 **********************************************************************/

	public static interface CompetitionAction {
		/**
		 * This function is called when a Competition is created and sets have
		 * been added. The function should implement what has to happen with the
		 * competition after creation and which result has to be returned
		 * 
		 * @param comp
		 * @param sets
		 * @return
		 */
		public Result createCompetition(Competition comp, Set[] sets);

		public Result closeCompetition(Competition comp,
				Map<String, String[]> form);

		/**
		 * This function is called in the renderCloseCompetition(Long id) controller
		 * The function should implement which view should be shown
		 * @param comp	The competition that has to be closed
		 * @return
		 */
		public Result renderCloseCompetition(Competition comp);

		/**
		 * This function is called in the render_create_competition()
		 * controller. It should specify which Result should be shown
		 * 
		 * @return
		 */
		public Result renderCreateCompetiton();

		/**
		 * this function is called in the rendder_open_competition() method
		 * It should specify which view should be shown
		 * @param comp	The competition that the person whiches to open
		 * @return
		 */
		public Result renderOpenCompetition(Competition comp);

		/**
		 * This function is called in the openCompetition() method
		 * IT should specify what has to happen when comp is opened
		 * @param comp	the competition that has to be opened
		 * @param form	the name - value pairs of input elements in the view rendered by the renderOpenCompetition() method
		 * @return
		 */
		public Result OpenCompetition(Competition comp,
				Map<String, String[]> form);
	}


	public static class TeacherCompetitionAction implements CompetitionAction {

		@Override
		public Result createCompetition(Competition comp, Set[] sets) {
			for(Set s : sets) {
				if(s.isRestricted!=CompetitionType.LOCAL || s.isHidden == true) {
					return badRequest();
				}
			}
			comp.addQuestionSets(sets);
			for (Set s : sets) {
				List<Class> classes = Class.find.where()
						.eq("teacher.bebrasId", session("bebrasId"))
						.eq("level", s.level).findList();
				for (Class c : classes) {
					c.addCompetition(comp);
				}
			}
			String url = routes.ProfilesController.seeProfile().url();
			return redirect(url);
		}

		public List<Set> getSets() {
			ArrayList<Set> list = new ArrayList<>();
			TreeSet<Set> sets = new TreeSet<Set>();
			Teacher t = Application.getCurrentlyLoggedInTeacher();
			List<Class> classes = Class.find.setMapKey("level").where()
					.eq("teacher.bebrasId", t.bebrasId).findList();
			for (Class c : classes) {
				List<Set> tempsets = Set.find.where().eq("level", c.level)
						.eq("isRestricted", CompetitionType.LOCAL)
						.eq("isHidden", false).findList();
				sets.addAll(tempsets);

			}
			list.addAll(sets);
			return list;
		}

		@Override
		public Result renderCreateCompetiton() {
			return ok(createCompetition.render(getSets()));
		}

		@Override
		public Result renderOpenCompetition(Competition comp) {
			List<Class> pclasses = comp
					.getParticipatingClasses(session("bebrasId"));
			List<Class> classes = comp
					.getNotParticipatingClasses(session("bebrasId"));
			if (pclasses.size() == 0 && classes.size() == 0) {
				return forbidden();
			}
			return ok(openCompetition.render(pclasses, classes, comp.id));
		}

		@Override
		public Result OpenCompetition(Competition comp,
				Map<String, String[]> map) {

			// if for some reason the competition isn't visible yet, the teacher
			// shouldn't be able to open it
			if (comp.isOpen != Competition.VISIBLE)
				return forbidden();

			// for each class the teacher has selected, the competition should
			// be opened.
			for (String s : map.keySet()) {
				Class c = Class.find.where()
						.eq("id", Long.parseLong(map.get(s)[0])).findUnique();
				c.openCompetition(comp);
			}
			
			String id = Application.getCurrentlyLoggedInTeacher().bebrasId;
			// return to the openCompetition page
			return ok(openCompetition.render(
					comp.getParticipatingClasses(id),
					comp.getNotParticipatingClasses(id), comp.id));
		}

		@Override
		public Result renderCloseCompetition(Competition comp) {
			Teacher t = Application.getCurrentlyLoggedInTeacher();
			List<Class> classes = comp.getParticipatingClasses(t.bebrasId);
			if(classes.size()==0) {
				return notFound();
			} else {
				return ok(closeCompetition.render(classes,comp));
			}
		}

		@Override
		public Result closeCompetition(Competition comp,
				Map<String, String[]> form) {
			for(String s : form.keySet()) {
				// For every chosen class the competition should be closed
				Class clazz = Class.findClassById(Long.parseLong(s));
				clazz.closeCompetition(comp);
				
			}
			// Redirect to the profile page
			String url = routes.ProfilesController.seeProfile().url();
			return redirect(url);
		}
	}

	public static class OrganizerCompetitionAction implements CompetitionAction {

		@Override
		public Result createCompetition(Competition comp, Set[] sets) {
			
			for(Set s : sets) {
				// Organizer can only create competitions with official question sets
				if(s.isRestricted!=CompetitionType.OFFICIAL) {
					return badRequest();
				}
					
			}
			
			
			comp.addQuestionSets(sets);
			for (Set s : sets) {
				List<Class> classes = Class.find.where().eq("level", s.level)
						.findList();
				for (Class c : classes) {
					c.addCompetition(comp);
				}
			}
			String url = routes.ProfilesController.seeProfile().url();
			return redirect(url);
		}

		public List<Set> getSets() {
			return Set.find.where()
					.eq("isRestricted", CompetitionType.OFFICIAL).findList();
		}

		@Override
		public Result renderCreateCompetiton() {
			return ok(createCompetition.render(getSets()));
		}

		@Override
		public Result renderOpenCompetition(Competition comp) {
			if(comp.isOpen == Competition.NOTVISIBLE && comp.compType==CompetitionType.OFFICIAL) {
				return ok(views.html.organizer.openCompetition.render(comp));
				
			}
			return forbidden();
		}

		@Override
		public Result OpenCompetition(Competition comp,
				Map<String, String[]> form) {
			ObjectNode result = Json.newObject();
			if(comp.isOpen == Competition.NOTVISIBLE && comp.compType == CompetitionType.OFFICIAL) {
				comp.isOpen = Competition.VISIBLE;
				comp.save();
				String url = routes.ProfilesController.seeProfile().url();
				return redirect(url);
			}
			
			result.put("forbidden","true");
			return forbidden(result);
		}

		@Override
		public Result renderCloseCompetition(Competition comp) {
			return ok(views.html.organizer.closeCompetition.render(comp));
		}

		@Override
		public Result closeCompetition(Competition comp,
				Map<String, String[]> form) {
			comp.isOpen=Competition.CLOSED;
			for(Class_Competition cc : Class_Competition.find.where().eq("competition.id", comp.id).findList()) {
				cc.close();
			}
			comp.save();
			String url = routes.ProfilesController.seeProfile().url();
			return redirect(url);
		}

	}

	public static class PupilCompetitionAction implements CompetitionAction {

		@Override
		public Result createCompetition(Competition comp, Set[] sets) {
			return badRequest();
		}

		public List<Set> getSets() {
			return null;
		}

		@Override
		public Result renderCreateCompetiton() {
			return badRequest();
		}

		@Override
		public Result renderOpenCompetition(Competition comp) {
			return badRequest();
		}

		@Override
		public Result OpenCompetition(Competition comp,
				Map<String, String[]> form) {
			return badRequest();
		}

		@Override
		public Result renderCloseCompetition(Competition comp) {
			return badRequest();
		}

		@Override
		public Result closeCompetition(Competition comp,
				Map<String, String[]> form) {
			return badRequest();
		}

	}

}
