package models;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import javax.persistence.*;

import play.db.ebean.Model;
import play.db.ebean.Model.Finder;
import utils.LangMessages;


@Entity
public class Set extends Model implements Comparable<Set> {
	
	@Id
	public Long id;
	public int timeLimit;  // Time limit in SECONDS
	public boolean isHidden;
	public Level level;
	public int length;
	public CompetitionType isRestricted;

    @OneToMany(cascade = CascadeType.ALL)
    @MapKey(name = "language")
    public Map<Language, Set_Language> setLanguages;

    public Set(int timeLimit, boolean isHidden, String level, CompetitionType isRestricted, Set_Language setLanguage){

        this.timeLimit = timeLimit;
        this.isHidden = isHidden;
        this.level = Level.getLevel(level);
        this.isRestricted = isRestricted;
        setLanguages = new TreeMap<>();
        setLanguages.put(setLanguage.language, setLanguage);
        this.save();
    }
    
    public Set(int timeLimit, boolean isHidden, String level, CompetitionType isRestricted, Map<Language, Set_Language> setLanguage){

        this.timeLimit = timeLimit;
        this.isHidden = isHidden;
        this.level = Level.getLevel(level);
        this.isRestricted = isRestricted;
        setLanguages = setLanguage;
        this.save();
    }
    
    public Set(){
    	
    }

    public List<Set_Question> getSetQuestions() {
        return Set.getSetQuestions(this);
    }

    public boolean contains(Question question) {
        for (Set_Question sq : getSetQuestions()) {
            if (question.equals(sq.question))
                return true;
        }

        return false;
    }

    public int size() {
        return getSetQuestions().size();
    }

    public int getInitialPoints() {
        int points = 0;

        for (Set_Question sq : getSetQuestions()) {
            points += Math.abs(sq.incorrectPoints);
        }

        return points;
    }

    public static Finder<Long,Set> find =
    		new Finder<Long,Set>(Long.class, Set.class);
    
    public static Set findById(Long setID){
    	return find.where().eq("id", setID).findUnique();
    }
    
    public static List<Set> findSetsByLevel(Level level){
    	return find.where().eq("level", level).findList();
    }

	public static List<Set_Question> getSetQuestions(Set set) {
        return Set_Question.find.where().eq("set", set).findList();
    }

    public static List<Question> getQuestions(Set set) {
        List<Set_Question> lsq = getSetQuestions(set);
        List<Question> lq = new ArrayList<>();
        for(Set_Question sq:lsq){
            lq.add(sq.question);
        }
        return lq;
    }
	/**
	 * returns the title for this set for a specified language
	 * @param language
	 * @return
	 */
	public String getTitle(Language language){
		return setLanguages.get(language).title;
	}
	
	/**
	 * returns the title for this set in the currently logged in user's preferred language.
	 * If that doesn't exist, it gives the title in the order given by the Language Enum
	 * 
	 * @return
	 */
	public String getTitle() {
			return getTitle(LangMessages.getLanguage(setLanguages.keySet()));
	}
	
	public Difficulties getQuestionDifficulty(Question question) {
		Set_Question sq = Set_Question.find.where().eq("set", this).eq("question", question).findUnique();
		if(sq == null) {
			return null;
		} else {
			return sq.difficulty;
		}
				
	}

	/**
	 * returns the amount of points one would get if he/she would answer question q correctly
	 * return -1 if question q isn't in this set
	 * @param q
	 * @return
	 */
	public int getCorrectPoints(Question q) {
		Set_Question sq = Set_Question.find.where().eq("set", this).eq("question", q).findUnique();
		if(sq == null) {
			return -1;
		} else {
			return sq.correctPoints;
		}
	}

    public int getAllCorrectPoints(){
        List<Set_Question> sqList = Set_Question.find.where().eq("set",this).findList();
        int p=0;
        for(Set_Question sq: sqList){
              p+=sq.correctPoints;
        }
        return p;
    }
	/**
	 * returns the amount of points one would loose if he/she would answer question q incorrectly
	 * return -1 if question q isn't in this set
	 * @param q
	 * @return
	 */
	public int getIncorrectPoints(Question q) {
		Set_Question sq = Set_Question.find.where().eq("set", this).eq("question", q).findUnique();
		if(sq == null) {
			return -1;
		} else {
			return sq.incorrectPoints;
		}
	}

	@Override
	public int compareTo(Set arg0) {
		return (int) (id-arg0.id);
	}
}
