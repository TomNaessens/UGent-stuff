package controllers;

import static play.data.Form.form;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import com.avaje.ebean.Ebean;
import com.avaje.ebean.SqlUpdate;
import org.codehaus.jackson.JsonNode;
import org.codehaus.jackson.node.ObjectNode;

import controllers.Application.Login;
import controllers.security.SecuredAdmin;
import controllers.security.SecuredOrganizer;

import models.Competition;
import models.CompetitionType;
import models.Difficulties;
import models.Language;
import models.Level;
import models.Person;
import models.Pupil;
import models.Question;
import models.Set;
import models.Set_Language;
import models.Set_Question;
import models.Teacher;
import play.data.DynamicForm;
import play.libs.Json;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import utils.LangMessages;
import views.html.common.login;
import views.html.organizer.*;
import views.html.*;


public class SetController extends Controller {

	@Security.Authenticated(SecuredOrganizer.class)
	public static Result renderComposeSet() {
		Set s = new Set();
		return ok(editQuestionSet.render(Question.getAllQuestions(), s));
	}
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result composeSet() {
		return editSet(new Long(-1));
	}
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result renderManageSets() {
		String bebrasId = session().get("bebrasId");
		String role = session().get("role");

		// Not authorized when role or bebras not set
		if (role == null || bebrasId == null) {
			return Application.login();
		}
		List<Set> sets = Set.find.all();
		return ok(ManageQuestionSets.render(sets));
	}

	/**
	 * Ajax handler that upgrades a set If the set is Local, the set will become
	 * Official If the set is Unrestricted, the set will become Local Official
	 * sets can't be upgraded
	 * 
	 * @param id
	 * @return
	 */
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result upgradeSet(Long id) {
		Set s = Set.findById(id);
		ObjectNode result = Json.newObject();
		if (s == null) {
			result.put("status", "bad ID");
			return badRequest(result);
		}
		CompetitionType ct = s.isRestricted;
		switch (ct) {
		case OFFICIAL:
			result.put("status", "can't upgrade");
			return ok(result);
		case LOCAL:
			s.isRestricted = CompetitionType.OFFICIAL;
			break;
		case UNRESTRICTED:
			s.isRestricted = CompetitionType.LOCAL;
			Competition.toggleUnrestrictedCompetition(s);
			break;
		}

		result.put("ok", s.isRestricted.toString());
		result.put("id", "" + id);
		s.save();
		return ok(result);

	}

	/**
	 * Ajax handler that downgrades a set If the set is Local, the set will
	 * become Unrestricted If the set is Official, the set will become Local
	 * Unrestricted sets can't be downgraded
	 * 
	 * @param id
	 * @return
	 */
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result downgradeSet(Long id) {
		Set s = Set.findById(id);
		ObjectNode result = Json.newObject();
		if (s == null) {
			result.put("status", "bad ID");
			return ok(result);
		}
		CompetitionType ct = s.isRestricted;
		switch (ct) {
		case OFFICIAL:
			s.isRestricted = CompetitionType.LOCAL;
			break;
		case LOCAL:
			s.isRestricted = CompetitionType.UNRESTRICTED;
			Competition.toggleUnrestrictedCompetition(s);
			break;
		case UNRESTRICTED:
			result.put("status", "can't downgrade");
			return ok(result);
		}

		result.put("ok", s.isRestricted.toString());
		result.put("id", "" + id);
		s.save();
		return ok(result);
	}
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result renderEditSet(Long id) {
		Set s = Set.findById(id);
		if (s == null) {
			return badRequest();
		}
		return ok(editQuestionSet.render(Question.getAllQuestions(), s));
	}

	
	/**
	 * Action to create or edit a question set
	 * @param id the id of the question set to be edited, if no question set exists with said id a new one will be created
	 * @return
	 */
	@Security.Authenticated(SecuredOrganizer.class)
	public static Result editSet(Long id) {
		// A boolean to specify if everything went ok
		boolean succes = true;
		
		// An Json node to specify errors etc.
		ObjectNode result = Json.newObject();
		
		/*
		 * The form that was submitted by the user. It contains:
		 * - several input boxes for the name of the set in different languages. key =  <LANGUAGE>::name
		 * - the competitionType of the set: key = compType
		 * - the level of the set: key = level
		 * - the timelimit (in seconds): key = timelimit
		 * - visibility of the set: key = visibility
		 * - selected questions: key = id of set, values should be in this order: id of question, difficulty of question, correct points, incorrect points
		 */
		Map<String, String[]> form = request().body().asFormUrlEncoded();
		
		// Map for the titles of the set
		Map<Language, Set_Language> names = new TreeMap<Language, Set_Language>();
		
		// Initializing attributes of set
		CompetitionType comptype = null;
		int timelimit = 0;
		Level level = null;
		boolean isHidden = false;
		
		// booleans to specify if it is a new set, if a competition type and a level was specified
		boolean newSet = false;
		boolean noCompType = true;
		boolean noLevel = true;
		
		Set set = Set.findById(id);
		
		// If the set doesn't exist, create a new one
		if(set == null) {
			set = new Set();
			newSet = true;
		}
		
		List<Set_Question> questions = new ArrayList<>();
		
			// iterate over the form keys
			for (String s : form.keySet()) {
				
				if (s.contains("::name")) {
					// the value is a title
					Language l = Language.valueOf(s.substring(0,
							s.indexOf("::")));
					if (!form.get(s)[0].equals("")) {
						names.put(l, new Set_Language(form.get(s)[0], l));
					}
				} else {
					if (s.equals("comptype")) {
							// the value is a competition type
							noCompType = false;
						try {
							String compTypeName = form.get(s)[0];
							comptype = CompetitionType.valueOf(compTypeName);
							if(comptype==null) {
								result.put("compType","error");
								succes = false;
							}
						} catch(Exception e) {
							result.put("compType","error");
							succes = false;
						}
						
						
					} else {
						if (s.equals("level")) {
							// the value is a level
							noLevel = false;
							try {
								level = Level.valueOf(form.get(s)[0]);
								if(level==null) {
									result.put("level", "error");
									succes = false;
								}
							} catch(Exception e) {
								result.put("level", "error");
								succes = false;
							}
						} else {
							if (s.equals("timelimit")) {
								// the  value is the timelimit (in minutes, gets converted to seconds)
								try {
									timelimit = Integer.parseInt(form.get(s)[0])*60;
									if(timelimit <= 0) {
										result.put("timelimit", "error");
										succes = false;
									}
								} catch(Exception e){
									result.put("timelimit", "error");
									succes = false;
								}
							} else {
								if (s.equals("visibility")) {
									
									try {
										isHidden = "true".equals(form.get(s)[0]) ? true : false;
									} catch(Exception e) {}
								} else {
									// the values are the specifics of the question
									String[] values = form.get(s);
									Long questionid;
									Question q = null;
									try {
										q = Question.getQuestion(Long
												.parseLong(values[0]));
									} catch(Exception e) {
										succes = false;
										
									}
									short correctPoints=0;
									
									// Try parsing correct points to a short
									try {
									correctPoints = (short) Math
											.abs(Short.parseShort(values[2]));
									} catch(Exception e) {
										// error
										result.put(""+q.id+"correctPoints", "error");
										succes = false;
									}
									short incorrectPoints=0;
									
									// Try parsing incorrect points to a short
									try {
										incorrectPoints = (short) Math
											.abs(Short.parseShort(values[3]));
									} catch (Exception e) {
										result.put(""+q.id+"incorrectPoints", "error");
										succes = false;
									}

									Set_Question sq = Set_Question.find.where().eq("set",set).eq("question",q).findUnique();
									Difficulties d = Difficulties.valueOf(values[1]);
									if(d==null) {
										succes = false;
										result.put(""+q.id+"diff", "error");
									}
									if(sq == null) {
										sq = new Set_Question(
											Difficulties.valueOf(values[1]),
											correctPoints, incorrectPoints, q,
											null);
											questions.add(sq);
									} else {
										sq.correctPoints = correctPoints;
										sq.incorrectPoints = incorrectPoints;
										sq.difficulty = Difficulties.valueOf(values[1]);
										questions.add(sq);
									}

								}
							}
						}
					}
				}
			}
		
		if(noCompType) {
			result.put("compType","error");
		}
		if(noLevel) {
			result.put("level", "error");
		}
		if (names.isEmpty()) {
			succes = false;
			result.put("emptyNames","error");
		}
		
		if (questions.isEmpty()) {
			succes = false;
			result.put("emptyQuestions", "error");
		}
		
		if(!succes) {
			result.put("fail", "true");
			return ok(result);
		}
		boolean wasUnrestricted = set.isRestricted == CompetitionType.UNRESTRICTED;
		set.isHidden = isHidden;
		set.isRestricted = comptype;
		set.level = level;
		set.timeLimit = timelimit;
		set.length = questions.size();			
		
		//Delete all the Set_Languages
		Map<Language, Set_Language> sls = set.setLanguages;
		for(Language l : new ArrayList<Language>(sls.keySet())){
			Set_Language sl  = sls.get(l);
			sls.remove(l);
			//sl.delete();
			sl.language = null;
		}
		set.setLanguages = names;
		
		
		// Delete all set that existed before editing questions
		List<Set_Question> sqs = Set_Question.find.where().eq("set.id",set.id).findList();
		for(Set_Question sq : sqs) {
		    sq.question = null;
			//sq.delete();
		}
		
		for (Set_Question sq : questions) {
			sq.set = set;
			sq.save();
		}
		set.save();
		boolean isUnrestricted = set.isRestricted == CompetitionType.UNRESTRICTED;
		
		if(newSet) {
			Competition.createUnrestrictedCompetition(set);
		}
		
		if(wasUnrestricted || isUnrestricted) {
			Competition.toggleUnrestrictedCompetition(set);
		}

		return ok(result);

	}
	@Security.Authenticated(SecuredOrganizer.class)
    public static Result deleteSet(long id) {
        Set questionSet = Set.findById(id);

        if (questionSet != null) {
            // Check if the only competitions that contain this questionSet are hidden unrestricted competitions
            List<Competition> competitions = Competition.find.where().eq("questionSets.id", questionSet.id).findList();

            int i=0;
            while (i < competitions.size() && competitions.get(i).compType == CompetitionType.UNRESTRICTED &&
                    competitions.get(i).isOpen != Competition.VISIBLE)
                i++;

            if (i < competitions.size()) {
                flash("warning", LangMessages.get("composeSet.cannotRemoveSet"));
            } else {
                // Delete the question set
                Ebean.delete(competitions);

                // TODO: Ugly fix to avoid foreign key constraints
                String[] queries = {
                    "DELETE FROM set_question WHERE set_id=" + questionSet.id,
                    "DELETE FROM set_language WHERE set_id=" + questionSet.id,
                    "DELETE FROM set where id=" + questionSet.id
                };

                for (String q : queries) {
                    SqlUpdate u = Ebean.createSqlUpdate(q);
                    Ebean.execute(u);
                 }
            }
        }

        return renderManageSets();
    }
    
    /*
     * returns the view of a set
     * @param id	the id of the set
     * @return		views.html.set gets rendered	
     */
    public static Result viewSet(Long id) {
    	Set s = Set.findById(id);
    	if(s == null || Application.getCurrentlyLoggedInPerson() instanceof Pupil) {
    		// the set doesn't exist or a pupil is trying to view the set
    		return badRequest();
    	}
    	
    	if(Application.getCurrentlyLoggedInPerson() instanceof Teacher) {
    		// A teacher can only view local question sets
    		if(!(s.isRestricted == CompetitionType.LOCAL)) 
    			return badRequest();
    	}
    	
    	List<Set_Question> sqs = Set.getSetQuestions(s);
    	return ok(views.html.Set.render(sqs,s));
    	
    }
}



    