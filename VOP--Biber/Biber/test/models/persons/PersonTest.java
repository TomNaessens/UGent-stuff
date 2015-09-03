package models.persons;

import com.sun.jna.platform.win32.Sspi;
import models.*;
import org.junit.*;
import static org.junit.Assert.*;
import play.test.WithApplication;
import utils.Hash;

import java.sql.Timestamp;

import static play.test.Helpers.*;

public class PersonTest extends WithApplication {

    /**
     * TESTS OF CLASS PERSON
     *
     * Methods tested:
     * getPerson()
     * constructors
     * isOnline()
     * generateRandomPassword()
     * generateBebrasId()
     * findPersonByEmail()
     */

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
    }
    
    /*
     * Test to check if all roles can be created, added and retrieved from the database
     */
    @Test
    public void createAndRetrieveDifferentUsers() {
        //Admin
        new Admin(null,"Bob","Bobsen","MALE","ENGLISH").save();
        Admin bob = Admin.find.where().eq("bebrasId", "bbobsen").findUnique();
        Admin bob2 = (Admin)Person.getPerson("bbobsen");
        assertNotNull(bob);
        assertNotNull(bob2);
        assertEquals(bob.bebrasId, bob2.bebrasId);
        
        //Teacher
        new Teacher(null,"Frank","Leraar","FEMALE","DUTCH","052252").save();
        Teacher frank = Teacher.find.where().eq("bebrasId", "fleraar").findUnique();
        Teacher frank2 = (Teacher)Person.getPerson("fleraar");
        assertNotNull(frank);
        assertNotNull(frank2);
        assertEquals(frank.bebrasId, frank2.bebrasId);
        
        //Pupil
        new Pupil(null,"Tom","Pupil","FEMALE","DUTCH",12,11,1991).save();
        Pupil tom = Pupil.find.where().eq("bebrasId", "tpupil").findUnique();
        Pupil tom2 = (Pupil)Person.getPerson("tpupil");
        assertNotNull(tom);
        assertNotNull(tom2);
        assertEquals(tom.bebrasId, tom2.bebrasId);
        
        //Organizer
        new Organizer(null,"Jan","Organizer","FEMALE","DUTCH").save();
        Organizer jan = Organizer.find.where().eq("bebrasId", "jorganizer").findUnique();
        Organizer jan2 = (Organizer)Person.getPerson("jorganizer");
        assertNotNull(jan);
        assertNotNull(jan2);
        assertEquals(jan.bebrasId, jan2.bebrasId);
    }

    @Test
    public void testMethods(){
        Person p = new Pupil("test@test55.com","Tom","Pupil","Male","DUTCH",12,11,1991);
        p.save();
        assertFalse(p.isOnline());
        assertTrue(Person.generateRandomPassword(15).length()==15);
        assertTrue(Person.generateBebrasId("Voornaam", "Achternaam").length()>0);
        assertNotNull(Person.findPersonByEmail("test@test55.com"));

    }



    
}
