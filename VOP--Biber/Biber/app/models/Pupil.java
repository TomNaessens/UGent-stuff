package models;


import java.util.ArrayList;
import java.util.List;

import javax.persistence.CascadeType;
import javax.persistence.Entity;
import javax.persistence.ManyToOne;
import javax.persistence.Version;

import org.joda.time.DateTime;

@Entity
public class Pupil extends Person {
	
	/*
	 * The class of the pupil
	 */
	@ManyToOne(cascade= CascadeType.ALL)
	public Class currentClass;
    @ManyToOne(cascade= CascadeType.ALL)
    public Class previousClass;
    public int startTime;
    public boolean isFinished;
    
    public boolean deactivated = false;
    
    public  DateTime dateOfBirth;
    
    public Pupil(String email, String firstName, String lastName, String gender, String language, 
            int dayOfBirth, int monthOfBirth,int yearOfBirth) {
        super(email, firstName, lastName, gender,language);
        this.dateOfBirth = new DateTime().withDate(yearOfBirth, monthOfBirth, dayOfBirth);
    }

    /**
     * Returns the status of the pupil in relation to
     * the ParticipationHistory
     *
     * @param history
     * @return
     */
    public Status getStatus(ParticipationHistory history) {
        if (history == null)
            return Status.READY;

        return history.isFinished() ? Status.FINISHED : Status.STARTED;
    }

    /**
     * @return  Returns the level of the class this pupil is associated with,
     *          or null in case this pupil is not associated with a class
     */
    public Level getLevel() {
        if (currentClass == null)
            return null;

        return currentClass.level;
    }
    
    /**
     * Creates a pupil with the given attributes, saves it to the DB and returns it. 
     * To be used for registrating a 'half-registered user'
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     * @param dayOfBirth
     * @param monthOfBirth
     * @param yearOfBirth
     * @return newly created Pupil
     */
    public static Pupil createPupil(String email, String firstName, String lastName, String gender, String language, 
            int dayOfBirth, int monthOfBirth,int yearOfBirth){
        Pupil p = new Pupil(email, firstName, lastName, gender, language, dayOfBirth, monthOfBirth, yearOfBirth);
        p.save();
        return p;
    }
    
    
    /**
     * Creates a pupil with the given attributes, assigns given class, BUT DOES NOT SAVE IT TO DATABASE. TO BE USED FOR REGISTERING PUPILS
     * To be used for registering pupils by file upload
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     * @param dayOfBirth
     * @param monthOfBirth
     * @param yearOfBirth
     * @return newly created Pupil
     */
    public static Pupil createPupilAndAssignClass(String email, String firstName, String lastName, String gender, String language, 
            int dayOfBirth, int monthOfBirth,int yearOfBirth, Class currentClass) throws Exception{
        Pupil p = new Pupil(email, firstName, lastName, gender, language, dayOfBirth, monthOfBirth, yearOfBirth);
        p.currentClass = currentClass;
        return p;
    }



    public static Finder<String,Pupil> find = new Finder<String,Pupil>(
            String.class, Pupil.class
    );

    /**
     * Find all pupils in the DB
     * @return list containing all pupils
     */
    public static List<Pupil> findAll(){
        return find.all();
    }
    
    /**
     * Find all open competitions for a pupil
     * @return list of open competitions
     */
    public List<Competition> findOpenCompetitions() {
        if (currentClass == null)
            return null;
        return currentClass.getOpenCompetitions();
    }

    /**
     * Find all pupils from a given class
     * @param cl
     * @return list containing all pupils from class
     */
    public static List<Pupil> findPupilsFromClass(Class cl){
        List<Pupil> list = find.where().eq("currentClass", cl).findList();
        if (list==null) {
            return new ArrayList<>();
        } else {
            return list;
        }
    }

    /**
     * Find all pupils that last year were in given class
     * @param cl
     * @return List containing all pupils of that class
     */
    public static List<Pupil> findPupilsFromPreviousClass(Class cl){
        List<Pupil> list = find.where().eq("previousClass", cl).findList();
        if (list==null) {
            return new ArrayList<>();
        } else {
            return list;
        }
    }

    /**
     * Find a pupil given his bebrasId
     * @param bebrasId
     * @return found Pupil or null
     */
    public static Pupil findPupilByBebrasID(String bebrasId){
        return find.where().eq("bebrasId", bebrasId).findUnique();
    }
    
    /**
     * Find pupil with given bebrasId. Use this method instead Person.getPerson(bebrasId), this one is less overhead in DB.
     * @param bebrasId
     * @return requested Pupil object if he exists, null otherwise
     */
    public static Pupil getPupil(String bebrasId){
        Pupil p = Pupil.find.where().eq("bebrasId", bebrasId).findUnique();
        if(p == null || p.deactivated) return null;
        return p;
    }

    /**
     * Returns an unfinished competition for the given Pupil in case
     * he has an unfinished competition, or null otherwise.
     *
     * @param pupil     The Pupil for which we want the competition
     * @return          An unfinished Competition, or null.
     */
    public static Competition getUnfinishedCompetition(Pupil pupil) {
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);

        if (history != null)
            return history.competition;

        return null;
    }

    /**
     *  Method to get the name of the user manual for the pupil role
     */
    @Override
    public String getManualName() {
        return "manual_pupil";
    }
}
