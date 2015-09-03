package models;

import java.sql.Timestamp;

import java.util.Random;
import java.util.regex.Pattern;

import javax.persistence.*;

import com.avaje.ebean.validation.NotNull;
import org.joda.time.DateTime;
import play.db.ebean.*;
import utils.Hash;

import play.data.validation.Constraints;
import play.data.validation.Constraints.Email;
import play.data.format.Formats;


@MappedSuperclass  
public abstract class Person extends Model  {
    
    
    private static final long serialVersionUID = 1L;
    private static final long ONLINEINTERVALMIN = 2;
    private static final Pattern rfc2822 = Pattern.compile(
            "^[a-z0-9!#$%&'*+/=?^_`{|}~-]+(?:\\.[a-z0-9!#$%&'*+/=?^_`{|}~-]+)*@(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\\.)+[a-z0-9](?:[a-z0-9-]*[a-z0-9])?$"
    );

    @Id
    @Constraints.Required
    @Formats.NonEmpty
    @Column(unique = true)
    public String bebrasId;

 
    /*@Constraints.Required
    @Formats.NonEmpty*/
    public String password;
    
    public String firstPassword;
    
    @Email
    public String email;

    public String firstName;
    public String lastName;
    public Gender gender;
    @NotNull
    public Language language;
    public Timestamp timestamp;
    /**
     * Constructor for a new Person. ONLY USE THIS FOR CREATION OF NEW PERSON!!! (-> e.g. register), not for retrieving anything else
     * @param email
     * @param firstName
     * @param lastName
     * @param gender should be a string corresponding with the messages enum.gender.male(.ab) or enum.gender.female(.ab)
     * @param language should be a string corresponding with the name of the enum 
     * @return new Person object, bebrasId generated from name and random password
     */
    public Person(String email, String firstName, String lastName, String gender,String language) {
        //Generate bebrasId and random temp password
        this.bebrasId = generateBebrasId(firstName, lastName);
        this.firstPassword = generateRandomPassword(10);
        this.password = Hash.createPassword(this.firstPassword);
        this.email = email;
        this.firstName = firstName;
        this.lastName = lastName;
        this.gender = Gender.getGender(gender);
        this.language = Language.valueOf(language);
    }

    public static Finder<Long,Person> find = new Finder<Long,Person>(
            Long.class, Person.class
    );
    
    /**
     * Changes the password of the person and saves to the DB.
     * @param password
     */
    public void changePassword(String password){
        this.password = Hash.createPassword(password);
        this.save();
    }

    /**
     * Authenticate a user, given his bebrasId and plaintext password
     * @param bebrasId
     * @param plaintextPassword
     * @return Null if authentication failed, person object (Organizer,Pupil, Teacher or Admin) if authentication succeeded
     */
    public static Person authenticate(String bebrasId, String plaintextPassword) {
        //Order of querying: Roles with the most users first, to minimize database overhead
        //Per role, check if person of this role with bebrasId exists, then check password
        //BebrasId should be unique, so when passwordcheck fails, no other DB-queries should be made -> immediately return null
        
        //Pupil
        Pupil p = Pupil.getPupil(bebrasId);
        if(p!=null){
            if (Hash.checkPassword(plaintextPassword, p.password)) {
                return p;
              }
            else return null;
        }
        
        //Teacher
        Teacher t = Teacher.find.where().eq("bebrasId", bebrasId).findUnique();
        if(t!=null){
            if (Hash.checkPassword(plaintextPassword, t.password)) {
                return t;
              }
            else return null;
        }
        
        //Organizer
        Organizer o = Organizer.find.where().eq("bebrasId", bebrasId).findUnique();
        if(o!=null){
            if (Hash.checkPassword(plaintextPassword, o.password)) {
                return o;
              }
            else return null;
        }
        //Admin
        Admin a = Admin.find.where().eq("bebrasId", bebrasId).findUnique();
        if(a!=null){
            if (Hash.checkPassword(plaintextPassword, a.password)) {
                return a;
              }
            else return null;
        } 
        return null;
    }

    /**
     * Searches the DB for a person, given his bebrasId
     * @param bebrasId
     * @return Null if no one with that BebrasId found, otherwise return person object (Organizer,Pupil, Teacher or Admin)
     */
    public static Person getPerson(String bebrasId) {
        //Query order determined by amount of users per role. Return immediately when found so that no other DB-queries executed
        if(bebrasId == null || bebrasId.equals("")){
            return null;
        }
        //Pupil
        Pupil p = Pupil.getPupil(bebrasId);
        if (p != null)
            return p;
        //Teacher
        Teacher t = Teacher.find.where().eq("bebrasId", bebrasId).findUnique();
        if (t != null)
            return t;
        //Organizer
        Organizer o = Organizer.find.where().eq("bebrasId", bebrasId).findUnique();
        if (o != null)
            return o;
        //Admin
        Admin a = Admin.find.where().eq("bebrasId", bebrasId).findUnique();
        if (a != null)
            return a;
        //None found
        return null;
    }
    
    /**
     * Searches the DB for a person, given his email
     * @param email
     * @return Null if no one with that email found, otherwise return person object (Organizer,Pupil, Teacher or Admin)
     */
    public static Person findPersonByEmail(String email){
        //Query order determined by amount of users per role. Return immediately when found so that no other DB-queries executed
        //Pupil
        if(email == null || email.equals(""))
            return null;
        Pupil p = Pupil.find.where().eq("email", email).findUnique();
        if (p != null && !p.deactivated)
            return p;
        //Teacher
        Teacher t = Teacher.find.where().eq("email", email).findUnique();
        if (t != null)
            return t;
        //Organizer
        Organizer o = Organizer.find.where().eq("email", email).findUnique();
        if (o != null)
            return o;
        //Admin
        Admin a = Admin.find.where().eq("email", email).findUnique();
        if (a != null)
            return a;
        //None found
        return null;
    }
    
    /**
     * Generates bebrasId from name
     */
    public static String generateBebrasId(String firstName, String lastName){
        String bebrasId = (firstName.charAt(0) + lastName).toLowerCase().replaceAll("\\s","");
        while(getPerson(bebrasId)!= null){
            int rand = (int) (Math.random()*10000); //number can be decreased or increased if necessary
            bebrasId = (firstName.charAt(0) + lastName + rand).toLowerCase().replaceAll("\\s","");
        }
        return bebrasId;
    }
    
    /**
     * Generates random password of desired length using numbers and lowercase chars
     */
    public static String generateRandomPassword(int length) 
    {
       String AB = "0123456789abcdefghijklmnopqrstuvwxyz";
       Random rnd = new Random();
       StringBuilder sb = new StringBuilder( length );
       for( int i = 0; i < length; i++ ) 
          sb.append( AB.charAt( rnd.nextInt(AB.length()) ) );
       return sb.toString();
    }

    /**
     * Determines wheter a person currently is logged in.
     * @return boolean
     */
    public boolean isOnline() {
        if(timestamp == null){
            return false;
        }
        long currentTime = System.currentTimeMillis();
        return (Math.abs(timestamp.getTime()- currentTime) <= (1000*60*1));
    }


    public abstract String getManualName();
    
    /**
     * Determines whether the given email has the corret format for an email address
     * @param email
     * @return true or false, depending on the correctness of the email address
     */
    public static boolean emailCorrect(String email){
        return rfc2822.matcher(email).matches();
    }
    
}
