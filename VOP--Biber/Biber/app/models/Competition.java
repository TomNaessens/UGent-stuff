package models;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;


import javax.persistence.*;

import org.jboss.netty.handler.codec.rtsp.RtspHeaders.Values;

import controllers.Application;


import play.db.ebean.Model;
import utils.LangMessages;

@Entity
public class Competition extends Model implements Comparable<Competition> {
	
	public static final short NOTVISIBLE = 0;
	public static final short VISIBLE = 1;
	public static final short CLOSED = 2;
	
	@Id
	public Long id;

    @OneToMany(cascade = CascadeType.ALL)
    @MapKey(name = "language")
    public Map<Language, Competition_Language> competitionLanguages;
	
	/**
	 * isOpen defines the state in which the competition is
	 * isOpen = 0 for official contests that are not visible to teachers
	 * isOpen = 1 for competitions ready to be opened. Visible to teachers 
	 * (or pupils/half registered users in case of unrestricted competitions)
	 * isOpen = 2 for official contests that are closed by organisors
	 */
	public short isOpen;
	
	public CompetitionType compType;

	
	@ManyToMany(cascade = CascadeType.ALL)
    @MapKey(name = "level")
	public Map<Level, Set> questionSets = new TreeMap<Level, Set>();

    private Competition(Competition_Language competitionLanguage) {
        competitionLanguages = new TreeMap<Language, Competition_Language>();
        competitionLanguages.put(competitionLanguage.language, competitionLanguage);
    }

    private Competition(Map<Language, Competition_Language> competitionLanguages){
    	this.competitionLanguages = competitionLanguages;

    }
    
	/**
	 * creates a new local competition
	 * @param Map of languages to Competition_Languages of the local competition
	 * @return a new closed local competition
	 */
	public static Competition createCompetition(
            Map<Language, Competition_Language> competitionLanguages,
            CompetitionType competitionType){

		Competition comp = new Competition(competitionLanguages);
		comp.isOpen = competitionType.visible();
		comp.compType = competitionType;
		comp.save();
		return comp;
	}

    /**
     * creates a new local competition
     * @param Competition_Language for the local competition
     * @return a new closed local competition
     */
    public static Competition createCompetition(
            Competition_Language competitionLanguage,
            CompetitionType competitionType){

        Competition comp = new Competition(competitionLanguage);
        comp.isOpen = competitionType.visible();
        comp.compType = competitionType;
        comp.save();
        return comp;
    }
	
    public static Finder<Long,Competition> find = 
    		new Finder<Long,Competition>(Long.class, Competition.class); 
    
    /**
     * Returns a list of all unrestricted quizzes, which are available for everyone to take, regardless of age
     * @return list of unrestricted quizzes
     */
    public static List<Competition> getUnrestrictedQuizzes(){
    	return find.where().eq("compType", CompetitionType.UNRESTRICTED).findList();
    }

    /**
     * Returns the title of this competition for the given Language
     *
     * @param language  The Language for which we want the title
     *
     * @return          Returns a String containg the title of
     *                  this competition for the given Language,
     *                  or null in case there is no title
     *                  for the given language.
     */
    public String getTitle(Language language) {
        Competition_Language cl = competitionLanguages.get(language);

        if (cl != null)
            return cl.title;

        return null;
    }
    
	/**
	 * returns the title for this competition in the currently logged in user's preferred language.
	 * If that doesn't exist, it gives the title in the order given by the Language Enum
	 * 
	 * @return
	 */
	public String getTitle() {
			return getTitle(LangMessages.getLanguage(competitionLanguages.keySet()));
	}

    /**
     * Returns a list of classes belonging to the teacher with the given bebrasId
     * where the status of the competitions for the classes is the given competitionStatus
     *
     * @param bebrasId              The bebras id of the Teacher
     * @param competitionStatus     The status of the competition given a class.
     *                              This can be one of the values Class_Competition.OPEN,
     *                              Class_Competition.CLOSED or Class_Competition.TERMINATED.
     *
     * @return                      Returns a list of classes belonging to the teacher with the given bebrasId
     *                              where the status of the competitions for the classes is the given
     *                              competitionStatus
     */
    private List<Class> getClasses(String bebrasId, short competitionStatus) {
        List<Class_Competition> classCompetitions = Class_Competition.find
                .where()
                    .eq("competition.id", id)
                    .eq("isOpen", competitionStatus)
                    .eq("currentClass.teacher.bebrasId", bebrasId)
                .findList();

        if (classCompetitions != null && classCompetitions.size() > 0) {
            List<Class> classes = new ArrayList<Class>(classCompetitions.size());

            // extract classes from class_competitions
            for (Class_Competition c : classCompetitions) {
                // TODO: this is really inefficient: we're querying for every single pupil. We should change this...
            	// This won't be used for pupils, but for teachers
                Class clazz = c.currentClass;
                classes.add(clazz);
            }

            return classes;
        }

        return new ArrayList<Class>();
    }
    
    /**
     * Returns a list of classes belonging to teacher with bebrasId, participating in the competition
     * @param teacher's bebrasId 
     * @return
     */
    public List<Class> getParticipatingClasses(String bebrasId) {
        return getClasses(bebrasId, Class_Competition.OPEN);
    }
    
    /**
     * Returns all classes of teacher with bebrasId @param, for who the competition hasn't been opened yet
     * @param bebrasId
     * @return
     */
    public List<Class> getNotParticipatingClasses(String bebrasId){
    	return getClasses(bebrasId, Class_Competition.CLOSED);
    }
    
    /**
     * this function returns true if the competition is currently open for a class of the currently logged in teacher
     * returns false if all or none classes of the teacher have taken the competition
     * @return
     */
    public boolean hasOpenClasses(){
    	Teacher teacher = Application.getCurrentlyLoggedInTeacher();
    	return !(Class_Competition.find
        .where()
            .eq("competition.id", id)
            .eq("isOpen", Class_Competition.OPEN)
            .eq("currentClass.teacher.bebrasId", teacher.bebrasId).findRowCount()==0);
    }
    
    
   /**
    * Returns the competition with id @param
    * @param competition id
    * @return the competition with
    */
   public static Competition findById(Long id){
    	return Competition.find.where().eq("id",id).findUnique();
    }
   
   /**
    * Adds questionsets to the competition.
    * No more questionsets than the amount of levels can be added.
    * No questionsets with the same level can be added.
    * @param sets
    * @return
    */
   public boolean addQuestionSets(Set[] sets) {
       boolean succeeded = true;
       
	   if(sets.length + questionSets.size() > Level.values().length)
		   return false;
       for (int i = 0; i < sets.length; ++i) {
           Set set = sets[i];
           
           
           if (questionSets.containsKey(set.level)) {  // we already have a set for this level
               succeeded = false;
           } else {
               questionSets.put(set.level, set);
           }
       }

	   saveManyToManyAssociations("questionSets");
	   save();
	   return succeeded;
   }

    /**
     * Returns all competitions
     * @return List of competitions
     */
    public static List<Competition> findAllCompetitions(){
        return Competition.find.all();
    }
    
    public static List<Competition> findOfficialCompetition(short isOpen) {
    	return find.where().eq("compType",CompetitionType.OFFICIAL).eq("isOpen",isOpen).findList();
    }
    

	@Override
	public int compareTo(Competition o) {
		return o.id.intValue() - this.id.intValue();
	}
	
	public static Competition getUnrestrictedCompetitionForSet(Set s) {
		return find.where().eq("compType", CompetitionType.UNRESTRICTED).eq("questionSets.id", s.id).findUnique();
	}
	
	/**
	 * Sets the unrestricted competition of set s to visible if s is of type Unrestricted
	 * sets it to notvisible otherwise
	 * @param s - the set for which the open competition has to be made visible/not visible
	 */
	public static void toggleUnrestrictedCompetition(Set s) {
		Competition comp = getUnrestrictedCompetitionForSet(s);
		if(comp != null) {
			if(s.isRestricted == CompetitionType.UNRESTRICTED && s.isHidden == false) {
				comp.isOpen = Competition.VISIBLE;
			} else {
				comp.isOpen = Competition.NOTVISIBLE;
			}
			comp.save();
		} 
		
	}
	
	/**
	 * creates a new unrestricted Competition for set S, which isn't visible
	 * @param s
	 */
	public static Competition createUnrestrictedCompetition(Set s) {
		Competition comp = getUnrestrictedCompetitionForSet(s);
		if(comp == null) {
			TreeMap<Language,Competition_Language> map = new TreeMap<Language, Competition_Language>();
			for(Language l : s.setLanguages.keySet()) {
				String title = s.setLanguages.get(l).title;
				map.put(l, new Competition_Language(title,l));
			}			
			comp = Competition.createCompetition(map, CompetitionType.UNRESTRICTED);
			Set[] setarray = new Set[1];
			setarray[0] = s;
			comp.addQuestionSets(setarray);
		}
		return comp;
	}
	
	/**
	 * An unrestricted competition should only have one questionset. This method returns the level of that set
	 * returns null if the competition isn't unrestricted or if it has more than 1 set. 
	 * @return
	 */
	public Level getLevelOfUnrestrictedCompetition() {
		if(compType != CompetitionType.UNRESTRICTED || questionSets.keySet().size() != 1) {
			return null;
		}
		
		for(Level level : Level.values()) {
			if(questionSets.keySet().contains(level)) {
				return level;
			}
		}
		return null;
	}
    


}
