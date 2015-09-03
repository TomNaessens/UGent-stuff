package models.persons;

import models.Organizer;
import models.School;
import models.Teacher;
import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import java.util.List;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class OtherPersonsTest extends WithApplication {

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
    }

    /**
     * TESTS OF CLASS TEACHER
     *
     * Methods tested:
     *      Constructor(5 args)
     *      getTeacher
     *      createTeacher()
     *      addSchool()
     */

    @Test
    public void testTeacher(){
        Teacher teach = new Teacher("at@at.at","First", "Last","MALE", "GERMAN","0051101");
        teach.save();
        List<Teacher> teachL = Teacher.find.where().eq("firstName", "First").eq("lastName", "Last").findList();
        assertTrue(teachL.size()>0);
        assertNotNull(Teacher.getTeacher("flast"));
        assertNotNull(Teacher.createTeacher("at@at.at","Second", "Last","MALE", "GERMAN","025"));
        teach.addSchool(new School("School","Gent","België", "Straat", "9000", "10"));
        teach.save();
        assertTrue(teach.schools.size()>0);

    }



    /**
     * TESTS OF CLASS ORGANIZER
     *
     * Methods tested:
     *      Constructor(5 args)
     *      getOrganizer()
     *      createOrganizer()
     *
     */

    @Test
    public void testOrganizer(){
        Organizer organ = new Organizer("at@at.at","First", "Last","MALE", "GERMAN");
        organ.save();
        List<Organizer> organL = Organizer.find.where().eq("firstName", "First").eq("lastName", "Last").findList();
        assertTrue(organL.size()>0);
        assertNotNull(Organizer.getOrganizer(organ.bebrasId));
        assertNotNull(Organizer.createOrganizer("a2t@a2t.at","Third", "Last","MALE", "GERMAN"));
    }
}
