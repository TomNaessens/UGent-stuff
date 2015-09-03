package controllers;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import controllers.security.SecuredAdmin;
import models.CompetitionType;
import models.Difficulties;
import models.Language;
import models.Level;
import models.Question;
import models.Set;
import models.Set_Language;
import models.Set_Question;
import play.mvc.Controller;
import play.mvc.Result;
import play.mvc.Security;
import views.html.organizer.*;
import controllers.security.*;

@Security.Authenticated(SecuredOrganizer.class)
public class ComposeSetAlternativeController extends Controller {

	
	public static Result renderComposeSet() {
		return ok(composeSetAlternative.render(Question.getAllQuestions()));
	}
	
	public static Result composeSet() {
		Map<String,String[]> form = request().body().asFormUrlEncoded();
		Map<Language,Set_Language> names = new TreeMap<Language, Set_Language>();
		CompetitionType comptype = null;
		int timelimit = 0;
		Level level = null;
		boolean isHidden = false;
		Set set = new Set();
		List<Set_Question> questions = new ArrayList<>();
		try {
		for(String s : form.keySet()) {
			if(s.contains("::name")) {
				Language l = Language.valueOf(s.substring(0,s.indexOf("::")));
				if(!form.get(s)[0].equals("")) {
					names.put(l, new Set_Language(form.get(s)[0], l));
				}
			} else {
				if(s.equals("comptype")) {
					comptype = CompetitionType.valueOf(form.get(s)[0]);
				} else {
					if(s.equals("level")) {
						level = Level.valueOf(form.get(s)[0]);
					} else {
						if(s.equals("timelimit")) {
								timelimit = Integer.parseInt(form.get(s)[0]);						
						} else {
							if(s.equals("visibility")) {
								isHidden = Boolean.getBoolean(form.get(s)[0]);
							} else {
								
								String[] values = form.get(s);
								Question q = Question.getQuestion(Long.parseLong(values[0]));
								
									short correctPoints = (short) Math.abs(Short.parseShort(values[2]));
									short incorrectPoints = (short) Math.abs(Short.parseShort(values[3]));
								
								
								Set_Question sq = new Set_Question
										(Difficulties.valueOf(values[1]),
										correctPoints,
										incorrectPoints,
										q,
										set);
								questions.add(sq);
								
							}
						}
					}
				}
			}
		}
		} catch(Exception e) {
			flash("fail","true");
			return ComposeSetAlternativeController.renderComposeSet();
		}
		if(comptype == null || level == null || timelimit < 0 || questions.isEmpty() || names.keySet().isEmpty()) {
			flash("fail","true");
			return ComposeSetAlternativeController.renderComposeSet();
		}
		set.isHidden = isHidden;
		set.isRestricted = comptype;
		set.level = level;
		set.timeLimit = timelimit;
		set.length = questions.size();
		set.setLanguages = names;
		for(Set_Question sq : questions) {
			sq.set = set;
			sq.save();
		}
		set.save();

		return ProfilesController.seeProfile();
	}
}
