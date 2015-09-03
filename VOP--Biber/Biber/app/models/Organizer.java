package models;

import javax.persistence.Entity;
import play.db.ebean.Model.Finder;

@Entity
public class Organizer extends Person{

    public Organizer(String email, String firstName, String lastName, String gender,String language) {
        super( email, firstName, lastName, gender,language);
    }

    public static Finder<String,Organizer> find = new Finder<String,Organizer>(
            String.class, Organizer.class
        );
    
    /**
     * Create a new organizer and save him in the database
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     * @return
     */
    public static Organizer createOrganizer(String email, String firstName, String lastName, String gender, String language){
        Organizer org = new Organizer(email, firstName, lastName, gender, language);
        org.save();
        return org;
    }
    
    
    /**
     * Find organizer with given bebrasId. Use this method instead Person.getPerson(bebrasId), this one is less overhead in DB.
     * @param bebrasId
     * @return requested Organizer object if he exists, null otherwise
     */
    public static Organizer getOrganizer(String bebrasId){
        return Organizer.find.where().eq("bebrasId", bebrasId).findUnique();
    }

    /**
     *  Method to get the name of the user manual for the organizer role
     */
    @Override
    public String getManualName() {
        return "manual_organizer";
    }
    
}
