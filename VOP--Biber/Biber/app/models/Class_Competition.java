package models;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.ManyToOne;

import play.db.ebean.Model;

import java.util.List;

@Entity
public class Class_Competition  extends Model {

	public static final short CLOSED = 0;
	public static final short OPEN = 1;
	public static final short TERMINATED = 2;
	
	@Id
	public Long id;
	@ManyToOne
	public Class currentClass;
    @ManyToOne
	public Competition competition;
    
	/**
	 * isOpen = 0 CLOSED
	 * isOpen = 1 OPEN
	 * isOpen = 2 TERMINATED
	 */
    public short isOpen;
    
	private Class_Competition(Class c, Competition compo){
		currentClass = c;
		competition = compo;
		isOpen = CLOSED;
		
	}
	
	/**
	 * Open the competition for the class
	 */
	protected void openCompetition(){
		isOpen = Class_Competition.OPEN;
		save();
		currentClass.update();
	}
	
	/**
	 * Close the competition for the class
	 */
	protected void closeCompetition(){
		isOpen = Class_Competition.TERMINATED;
		save();
		currentClass.update();
	}
	
	/**
	 * Creates a new Class_Competition entity which defines
	 * that a class can participate in a competition if
	 * isOpen = Class_Competition.OPEN.
	 * the class_competition is saved to the database
	 * @param c the class
	 * @param competition the competition
	 */
	public static void createClassCompetition(Class c, Competition competition){
		Class_Competition cc = new Class_Competition(c, competition);
		cc.save();
	}

    /**
     * Returns all the available Class_CompetitionS for a given Class
     * @param clazz     The Class for which we want the available Class_CompetitionS
     * @return          Returns a List of available Class_CompetitionS for a given Class
     */
    public static List<Class_Competition> getClassCompetitions(Class clazz) {
        return find.where()
                    .eq("currentClass", clazz)
                .findList();
    }
    
    /**
     * Returns all open competitions visible for pupils for a given class
     * @param clazz		The class for which we want the open Class_Competitions
     * @return			Returns a List of open Class_Competiitons
     */
    public static List<Class_Competition> getClassCompetitions(Class clazz, short isOpen) {
    	return find.where().eq("currentClass", clazz).eq("isOpen",isOpen).ne("competition.isOpen", Competition.NOTVISIBLE).findList();
    }
	
    public static Class_Competition findClassCompetition(Long competitionId, Long classId) {
    	return find.where().eq("currentClass.id",classId).eq("competition.id", competitionId).findUnique();
    			
    }
	
	 public static Model.Finder<Long,Class_Competition> find = new Model.Finder(Long.class, Class_Competition.class);

	public void close() {
		isOpen = TERMINATED;
		save();
		
	}
	
}
