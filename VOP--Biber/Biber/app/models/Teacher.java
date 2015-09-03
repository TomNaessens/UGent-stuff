package models;

import java.util.ArrayList;
import java.util.List;

import javax.persistence.CascadeType;
import javax.persistence.Entity;
import javax.persistence.JoinTable;
import javax.persistence.ManyToMany;
import javax.persistence.OneToMany;

import play.db.ebean.Model.Finder;

@Entity
public class Teacher extends Person {
    
    /**
     * List of schools the teacher is responsible for (many to many relationship).
     */
    //ALWAYS SAVEMANYTOMANY WHEN SOMETHING CHANGES IN THIS LIST
    @ManyToMany(cascade=CascadeType.ALL)
    public List<School> schools = new ArrayList<School>();
    
    public String telephone;
    
    /**
     * Normal constructor for teacher
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     */
    public Teacher(String email,String firstName, String lastName,String gender, String language, String telephone){
        super(email,firstName,lastName,gender,language);
        this.telephone = telephone;
    }

    public static Finder<String,Teacher> find = new Finder<String,Teacher>(
            String.class, Teacher.class
        );
    
    /**
     * Find teacher with given bebrasId. Use this method instead Person.getPerson(bebrasId), this one is less overhead in DB.
     * @param bebrasId
     * @return requested Teacher object if he exists, null otherwise
     */
    public static Teacher getTeacher(String bebrasId){
        return Teacher.find.where().eq("bebrasId", bebrasId).findUnique();
    }
    
    /**
     * Add given school to the teacher.
     * @param school
     */
    public void addSchool(School school){
        schools.add(school);
        this.saveManyToManyAssociations("schools");
    }
    
    /**
     * Creates a new teacher and saves it to the database.
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     * @return The new teacher object
     */
    public static Teacher createTeacher(String email, String firstName, String lastName, String gender, String language, String telephone){
        Teacher t = new Teacher(email, firstName, lastName, gender, language, telephone);
        t.save();
        t.saveManyToManyAssociations("schools");
        return t;
    }

    /**
     * Creates a new teacher and saves it to the database. Also adds given schools for the teacher.
     * @param email
     * @param firstName
     * @param lastName
     * @param gender
     * @param language
     * @param schools
     * @return The new teacher object
     */
    public static Teacher createTeacher(String email, String firstName, String lastName, String gender, String language,String telephone, List<School> schools){
        Teacher t = new Teacher(email, firstName, lastName, gender, language, telephone);
        t.save();
        for(School s: schools)
            t.addSchool(s);
        return t;
    }

    /**
     *  Method to get the name of the user manual for the teacher role
     */
    @Override
    public String getManualName() {
        return "manual_teacher";
    }
    
    /**
     * Returns all teacher from a school with given id.
     * @param schoolId
     * @return list of teachers
     */
    public static List<Teacher> getTeachersFromSchool(long schoolId){
        List<Teacher> list = find.all();
        List<Teacher> returnList = new ArrayList<Teacher>();
        for(Teacher t: list){
            boolean add = false;
            for(School s: t.schools){
                if(s.id == schoolId){
                    add = true;
                    break;
                }
            }
            if(add)
                returnList.add(t);
        }
        return returnList;
    } 
}
