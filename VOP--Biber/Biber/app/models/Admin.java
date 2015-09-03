package models;

import javax.persistence.Entity;

import play.db.ebean.Model.Finder;

@Entity
public class Admin extends Person{

    public Admin(String email, String firstName, String lastName, String gender,String language) {
        super(email, firstName, lastName, gender,language);
    }

    public static Finder<String,Admin> find = new Finder<String,Admin>(
            String.class, Admin.class
        );
    
    /**
     * Find admin with given bebrasId. Use this method instead Person.getPerson(bebrasId), this one is less overhead in DB.
     * @param bebrasId
     * @return requested Admin object if he exists, null otherwise
     */
    public static Admin getAdmin(String bebrasId){
        return Admin.find.where().eq("bebrasId", bebrasId).findUnique();
    }

    /**
     *  Method to get the name of the user manual for the admin role
     */
    @Override
    public String getManualName() {
        return "manual_admin";
    }
}
