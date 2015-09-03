package controllers;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.status;

import java.util.*;

import models.*;

import models.Class;
import models.Set;
import org.junit.Before;
import org.junit.Test;

import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

import com.avaje.ebean.Ebean;

/**
 * Test class for some functions of the organizer role
 *      Tested: registerSchool
 *              endYear
 */
public class OrganizerControllerTest extends WithApplication{
    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        // Because yaml doesn't uses default empty constructor
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            // This is logintest, so assume that account is already activated by
            // setting firstpassword to empty string
            person.firstPassword = "";
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
        Ebean.save(all.get("competitions"));
        Ebean.save(all.get("classes"));
        Ebean.save(all.get("questions"));
    }
    
    /**
     * TODO: because it's not easy to give multiple schools to the request
     */
    @Test
    public void registerTeacherTest(){
        
    }
    
    @Test
    public void registerSchoolTest(){
        Map<String, String> map = new HashMap<String, String>() {
            {
                put("name", "hogent");
                put("city", "gent");
                put("zipCode", "9000");
                put("street", "straat");
                put("number", "1");
                put("country", "Belgie");
            }
        };
        Result result = callAction(controllers.routes.ref.OrganizerController.registerSchool(),fakeRequest().withSession("bebrasId", "ebral").withSession("role", "organizer")
                    .withFormUrlEncodedBody(map));
        assertEquals(303,status(result));
        School school = School.findSchool("Belgie", "9000", "straat", "1");
        assertNotNull(school);
    }

    @Test
    public void endYearTest(){
        Result result = callAction(controllers.routes.ref.OrganizerController.endYear(),fakeRequest().withSession("bebrasId", "ebral").withSession("role", "organizer"));
        assertEquals(200,status(result));
        List<Class> list = new ArrayList<>();
        List<Pupil> pupils = Pupil.findAll();
        for (Pupil p: pupils) {
            if (p.currentClass!=null) {
                list.add(p.currentClass);
            }
        }
        assertTrue(list.size()==0);
    }
}
