package controllers;

import static org.junit.Assert.*;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.status;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import models.Class;
import models.Person;
import models.Pupil;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;
import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

/**
 * Test class for the reset password functionality
 */
public class RegisterPupilTest extends WithApplication{

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        if (Teacher.find.findRowCount() == 0) {
            Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");

            //Save Competitions
            Ebean.save(all.get("competitions"));
            //Load schools 
            Ebean.save(all.get("schools"));
            
            // Load persons from test-data file
            List<Person> persons = (List<Person>) (Object) all.get("persons");
            for (Person p : persons) {
                p.firstPassword = "";
                p.password = Hash.createPassword("secret");
                Ebean.save(p);
                if(p instanceof Teacher)
                    Ebean.saveManyToManyAssociations(p, "schools");
            }
            //For other data, see up
            Ebean.save(all.get("classes"));
        }
    }
    
    
    @Test
    public void registerSinglePupilTest() {
        Teacher t = Teacher.getTeacher("hswimberghe");

        Map<String, String> map = new HashMap<String, String>() {
            {
                put("firstName", "Tom");
                put("lastName", "Tomsen");
                put("email", "");
                put("gender", "MALE");
                put("language", "ENGLISH");
                put("dateOfBirth", "12/11/1991");
            }
        };
        // Register single pupil
        Class foundClass = Class.findClassesByTeacher(t).get(0);
        Result result = callAction(
                controllers.routes.ref.TeacherController
                        .registerSinglePupil(foundClass.id),
                fakeRequest().withSession("bebrasId", "hswimberghe")
                        .withSession("role", "teacher")
                        .withFormUrlEncodedBody(map));
        assertEquals(303, status(result));
        assertTrue(Pupil.findPupilsFromClass(foundClass).contains(
                Pupil.findPupilByBebrasID("ttomsen")));
        
        //delete class
        Pupil p = Pupil.findPupilByBebrasID("ttomsen");
        p.currentClass = null;
        p.save();
    }

}
