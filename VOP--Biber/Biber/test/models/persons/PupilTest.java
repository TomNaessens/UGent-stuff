package models.persons;


import models.*;
import models.Class;
import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class PupilTest extends WithApplication {

    /**
     * TESTS OF CLASS PUPIL
     *
     * Interaction between pupil, school and class
     *
     * Tested:
     *      Constructor
     *      currentClass
     *      findPupilByBebrasId()
     *      getPupil()
     *      findPupilsFromClass()
     *      createPupilAndAssignClass()
     *      createPupil()
     *
     */

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
    }

    @Test
    public void testPupil(){
        Pupil pupil = new Pupil("mijnEmail@internet.com", "My", "Name", "FEMALE", "DUTCH", 1,1, 2000 );
        pupil.save();
        School sch = new School("School","Gent","België", "Straat", "9000", "2");
        School sch2 = School.findSchool("België", "9000", "Straat", "2");
        models.Class cl = new Class("5e1","JEDI",2000, sch2, null );
        cl.save();
        pupil.currentClass=cl;
        assertNotNull(pupil);
        assertNotNull(pupil.currentClass);
    }

    @Test
    public void testPupil2(){
        Pupil pupil = new Pupil("mijnEmail@internet.com", "My", "Name", "FEMALE", "DUTCH", 1,1, 2000 );
        pupil.save();
        Pupil p = Pupil.find.where().eq("bebrasId", "mname").findUnique();
        assertEquals(pupil, p);
        Pupil p2 = Pupil.getPupil("mname");
        assertEquals(pupil, p2);
        Pupil p3 = Pupil.findPupilByBebrasID("mname");
        assertEquals(pupil, p3);

    }

    @Test
    public void testPupil3(){
        Pupil pup = Pupil.createPupil("mijnEmail@internet.com", "My", "Name", "MALE", "DUTCH", 1,1, 2002);
        pup.save();
        School sch = new School("School","Gent","België", "Straat", "9000", "2");
        sch.save();
        Class cl = new Class("5e1","WOOKIE",2000, sch, null );
        cl.save();
        Pupil pup2;
        try {
            pup2 = Pupil.createPupilAndAssignClass("mijnEmail@internet.com", "My", "Nam2e", "MALE", "DUTCH", 1,5, 1902, cl);
            pup2.save();
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        assertTrue(Pupil.findPupilsFromClass(cl).size()>0);
    }


}
