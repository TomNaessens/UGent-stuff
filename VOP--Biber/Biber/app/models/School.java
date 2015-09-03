package models;

import play.db.ebean.*;
import javax.persistence.*;
import java.util.ArrayList;
import java.util.List;

@Entity
public class School extends Model {

    @Id
    public Long id;
    public String name;
    public String city;
    /**
     * A String because there exists zipCodes with letters in some countries
     */
    public String zipCode;
    public String country;
    public String street;
    /**
     * A String because there exists 17b, 210a, etc..
     */
    public String number;
    

    /**
     * Creates a new school, returns it, and saves it to the database.
     * @param name
     * @param city
     * @param country
     * @param street
     * @param zipCode
     * @param number
     */
    public School(String name, String city, String country, String street, String zipCode, String number) {
        this.name = name;
        this.city = city;
        this.country = country;
        this.street = street;
        this.zipCode = zipCode;
        this.number = number;
        this.save();
    }

    public static Model.Finder<Long,School> find = new Model.Finder(Long.class, School.class);

    /**
     * Find a school given his address.
     * @return the school
     */
    public static School findSchool(String country, String zipCode, String street, String number){
        return find.where().eq("street", street).eq("country", country).eq("zipCode",zipCode).eq("number",number).findUnique();
    }
    
    /**
     * Find a school given his unique ID.
     * @return the school
     */
    public static School findSchool(long ID){
        return find.where().eq("id", ID).findUnique();
    }
    
    /**
     * Return all schools
     * @return
     */
    public static List<School> allSchools(){
        return find.all();
    }
    
    /**
     * Returns list of schools excluding the ones the teacher already has
     * @param teacher
     * @return null if no schools, else list of schools
     */
    public static List<School> allSchoolsNotHavingTeacher(Teacher teacher){
        List<School> schools = new ArrayList<School>();
        for(School s: allSchools()){
            if(!teacher.schools.contains(s))
                schools.add(s);
        }
        if(schools.size() == 0) return null;
        return schools;
    }

    @Override
    public String toString(){
        return name+"\nAddress: "+street+" "+number+" "+zipCode+" "+city;
    }
}