package models;


import org.joda.time.DateTime;
import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import java.util.List;

import static models.School.findSchool;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class ClassSchoolTest extends WithApplication {

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
    }

    /**
     * TESTS OF CLASS SCHOOL
     *
     * Methods tested:
     * Constructor(6 args)
     * toString()
     * findSchool(Long id)
     * findSchool(address..)
     */

    @Test
    public void testSchool() {
        School sch = new School("School", "Gent", "België", "Straat", "9000", "1");
        sch.save();
        List<School> lijst = School.find.where().eq("name", "School").findList();
        assertTrue(lijst.size() > 0);
        assertNotNull(findSchool("België", "9000", "Straat", "1"));
        assertEquals("School\nAddress: Straat 1 9000 Gent", sch.toString());

    }

    @Test
    public void testSchool2() {
        School cl = new School("School", "Gent", "Belgie", "straat", "9000", "1");
        cl.save();
        assertNotNull(School.findSchool(cl.id));
        assertNotNull(School.findSchool("Belgie", "9000", "straat", "1"));
    }


    /**
     * TESTS OF CLASS CLASS
     *
     * Methods tested:
     * Constructor(5 args)
     * different finds
     * findClassById()
     * findSchoolClasses()
     * findClassesByTeacher()
     * findTeacherClasses()
     * createClass()
     *
     * Methods 2 (for tests see CompetitionTest.java):
     * openCompetition()
     * getOpenCompetitions()
     * addCompetition()
     * getAddedCompetitions()
     */

    @Test
    public void testClassWithoutTeacher() {
        int year = DateTime.now().getYear();
        // so when adding a class in january 2013, year should be 2012
        if (DateTime.now().getMonthOfYear() < 9) {
            year--;
        }
        School sch = new School("School", "Gent", "België", "Straat", "9000", "2");
        sch.save();
        Class cl = new Class("5e1", "WOOKIE", year, sch, null);
        cl.save();
        List<Class> myCl = Class.find.where().eq("name", "5e1").findList();
        List<Class> myCl2 = Class.find.where().eq("school", sch).findList();
        List<Class> myCl3 = Class.findSchoolClasses(sch.id);
        assertTrue(myCl.size() > 0);
        assertTrue(myCl2.size() > 0);
        assertTrue(myCl3.size() > 0);

    }


    @Test
    public void testClassWithTeacher() {
        School sch = new School("School", "Gent", "België", "Straat", "9000", "2");
        sch.save();
        Teacher teach = new Teacher("at@at.at", "First", "Last", "MALE", "GERMAN","055551");
        teach.save();
        Class cl = new Class("5e1", "PADAWAN", 2000, sch, teach);
        cl.save();
        List<Class> myCl = Class.find.where().eq("name", "5e1").findList();
        assertTrue(myCl.size() > 0);
        assertEquals(Class.findClassesByTeacher(teach).size(),1);
    }

    @Test
    public void testClass1() {
        Class cl =  Class.createClass("Name", "EWOK", 2000, null, null);
        cl.save();
        assertNotNull(Class.findClassById(cl.id));
    }


}
