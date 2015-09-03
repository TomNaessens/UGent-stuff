package models;

import org.joda.time.DateTime;
import play.db.ebean.*;
import javax.persistence.*;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

@Entity
public class Class extends Model {

    @Id
    public Long id;
    public String name;
    public Level level;
    public int beginYear; // e.g. 2013
    @ManyToOne
    public School school;
    @ManyToOne
    public Teacher teacher;

    public Class(String name, String level, int beginYear, School school, Teacher teacher) {
        this.name = name;
        this.level = Level.getLevel(level);
        this.beginYear = beginYear;
        this.school = school;
        this.teacher = teacher;
    }

    public List<Competition> getAvailableCompetitions() {
    	
        List<Class_Competition> classcomps =  Class_Competition.getClassCompetitions(this);
        ArrayList<Competition> comps = new ArrayList<>();
        for(Class_Competition cc : classcomps) {
        	comps.add(cc.competition);
        }
        return comps;
    }
    public List<Competition> getOpenCompetitions(){
    	List<Class_Competition> cc = Class_Competition.getClassCompetitions(this,Class_Competition.OPEN);
    	List<Competition> comps = new ArrayList<Competition>();
    	for(Class_Competition c : cc) {
    		comps.add(c.competition);
    	}
    	return comps;
    }

    public List<Competition> getFinishedCompetitions(){
        List<Class_Competition> cc = Class_Competition.getClassCompetitions(this,Class_Competition.TERMINATED);
        List<Competition> comps = new ArrayList<Competition>();
        for(Class_Competition c : cc) {
            if (CompetitionType.OFFICIAL.equals(c.competition.compType)) {
                if (c.competition.isOpen==2) {
                   comps.add(c.competition);
                }
            } else {
                comps.add(c.competition);
            }
        }
        return comps;
    }

    
    public List<Competition> getTerminatedCompetitions(){
    	List<Class_Competition> cc = Class_Competition.getClassCompetitions(this,Class_Competition.TERMINATED);
    	List<Competition> comps = new ArrayList<Competition>();
    	for(Class_Competition c : cc) {
    		comps.add(c.competition);
    	}
    	return comps;   	
    }
    
    public List<Competition> getClosedCompetitions(){
    	List<Class_Competition> cc = Class_Competition.getClassCompetitions(this,Class_Competition.CLOSED);
    	List<Competition> comps = new ArrayList<Competition>();
    	for(Class_Competition c : cc) {
    		comps.add(c.competition);
    	}
    	return comps;
    }

    public static List<Pupil> getPupils(Class c){
        return Pupil.find.where().eq("currentClass",c).findList();
    }

    public static Model.Finder<Long, Class> find = new Model.Finder<Long, Class>(
            Long.class, Class.class);

    public static List<Class> findClassesByTeacher(Teacher t){
        return find.where().eq("teacher", t).findList();
    }

    public static Class findClassById(Long id){
        return find.where().eq("id", id).findUnique();


    }

    @Override
    public String toString() {
        return name + ", " + beginYear + " from " + school + ", level: " + level;
    }

    /**
     * Creates a new class and saves it immediately to the DB.
     * 
     * @param name
     * @param level
     * @param school
     * @param teacher
     * @return the newly created class.
     */
    public static Class createClass(String name, String level, int beginYear, School school,
            Teacher teacher) {
        Class newClass = new Class(name, level, beginYear, school, teacher);
        newClass.save();
        
        // For the new class, all competitions that haven't been officially closed by an organisor should be added to the class
        List<Class> teacherClasses = Class.findClassesByTeacher(teacher);
        java.util.Set<Competition> competitions = new TreeSet<>();
        for(Class c : teacherClasses) {
        	if(c.level == newClass.level) {
        		competitions.addAll(c.getClosedCompetitions());
        		competitions.addAll(c.getOpenCompetitions());
        		competitions.addAll(c.getTerminatedCompetitions());
        		break;
        	}
        }
        competitions.addAll(Competition.find.where().eq("isOpen", Competition.VISIBLE).eq("compType", CompetitionType.OFFICIAL).findList());
        
        //remove all competitions that have been closed officialy by an organisor
        competitions.removeAll(Competition.find.where().eq("isOpen",Competition.CLOSED).findList());
        
        
        for(Competition comp : competitions) {
        	newClass.addCompetition(comp);
        	for(Class c : comp.getNotParticipatingClasses(teacher.bebrasId)) {
        		System.err.println(c);
        	}
        }
        
        
        
        return newClass;
    }

    /**
     * @param teacherBebrasID
     * @return A list of all the classes the teacher is responsible for
     */
    public static List<Class> findTeacherClasses(String teacherBebrasID) {
        return find.where().eq("teacher.bebrasId", teacherBebrasID).findList();
    }

    /**
     * Returns the list of classes existing in the requested school for the current schoolyear
     * @param schoolId, id of the school
     * @return List of classes existing in the school with given id in the current year
     */
    public static List<Class> findSchoolClasses(long schoolId) {
        int year = DateTime.now().getYear();
        // so when adding a class in january 2013, year should be 2012
        if (DateTime.now().getMonthOfYear() < 9) {
            year--;
        }
        return  find.where().eq("school.id", schoolId).eq("beginYear",year).findList();

    }

    /**
     * Returns the list of classes existing in the requested school for the current schoolyear
     * @param schoolId, id of the school
     * @return List of classes existing in the school with given id in the current year
     */
    public static List<Class> findPreviousSchoolClasses(long schoolId) {
        int year = DateTime.now().getYear();
        // so when adding a class in january 2013, year should be 2012
        if (DateTime.now().getMonthOfYear() < 9) {
            year--;
        }
        //previous year
        year--;
        return find.where().eq("school.id", schoolId).eq("beginYear",year).findList();
    }

    /**
     * adds the competition to the available competitions list. This list is
     * still closed
     * 
     * @param competition
     */
    public void addCompetition(Competition competition) {
        Class_Competition.createClassCompetition(this, competition);
    }

    /**
     * opens the competition for this class
     * 
     * @param competition
     */
    public void openCompetition(Competition competition) {
        Class_Competition cc = Class_Competition.find.where()
                .eq("competition.id", competition.id)
                .eq("currentClass.id", id).findUnique();
        if(cc!=null) {
        	cc.openCompetition();
        }
    }

	public void closeCompetition(Competition competition) {
		Class_Competition cc = Class_Competition.findClassCompetition(competition.id, id);
		cc.close();
		
	}

}
