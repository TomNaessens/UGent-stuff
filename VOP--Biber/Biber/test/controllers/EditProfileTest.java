package controllers;

import static org.junit.Assert.*;
import static org.junit.Assert.assertNotNull;
import static play.test.Helpers.*;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import models.*;
import org.junit.Before;
import org.junit.Test;
import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;
import com.avaje.ebean.Ebean;
import utils.LangMessages;

/**
 * Test class for the controller and views of the edit Profile functionality.
 * Test class for the main Profile Page.
 */
public class EditProfileTest extends WithApplication{
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
     * Testing of editProfiles for all roles.
     */
    @Test
    public void editProfileTest(){
        Pupil p = new Pupil("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH",1,1,1998);
        p.save();
        Teacher t = new Teacher("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH","05252");
        t.save();
        Organizer o = new Organizer("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH");
        o.save();
        Admin a = new Admin("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH");
        a.save();
        String id1 = p.bebrasId;
        String id2 = t.bebrasId;
        String id3 = o.bebrasId;
        String id4 = a.bebrasId;
        Map<String, String> map = new HashMap<String, String>() {
            {
                put("First Name", "MyName2");
                put("Last Name", "MyLastName2");
                put("Gender", "FEMALE");
                put("Language", "DUTCH");
                put("Email", "test2@test2.com");
            }
        };
        Result result1 = callAction(controllers.routes.ref.ProfilesController.submitChangesProfile(),fakeRequest().withSession("bebrasId", id1).withSession("role", "pupil")
                .withFormUrlEncodedBody(map));
        assertEquals(200,status(result1));
        Result result2 = callAction(controllers.routes.ref.ProfilesController.submitChangesProfile(),fakeRequest().withSession("bebrasId", id2).withSession("role", "teacher")
                .withFormUrlEncodedBody(map));
        assertEquals(200,status(result2));
        Result result3 = callAction(controllers.routes.ref.ProfilesController.submitChangesProfile(),fakeRequest().withSession("bebrasId", id3).withSession("role", "organizer")
                .withFormUrlEncodedBody(map));
        assertEquals(200,status(result3));
        Result result4 = callAction(controllers.routes.ref.ProfilesController.submitChangesProfile(),fakeRequest().withSession("bebrasId", id4).withSession("role", "admin")
                .withFormUrlEncodedBody(map));
        assertEquals(200,status(result4));
        Pupil p2 = Pupil.getPupil(id1);
        Teacher t2 = Teacher.getTeacher(id2);
        Organizer o2 = Organizer.getOrganizer(id3);
        Admin a2 = Admin.getAdmin(id4);

        assertEquals(p2.firstName, "MyName2");
        assertEquals(p2.lastName, "MyLastName2");
        assertEquals(p2.gender, Gender.FEMALE);
        assertEquals(p2.language, Language.DUTCH);
        assertEquals(p2.email, "test2@test2.com");

        assertEquals(t2.firstName, "MyName2");
        assertEquals(t2.lastName, "MyLastName2");
        assertEquals(t2.gender, Gender.FEMALE);
        assertEquals(t2.language, Language.DUTCH);
        assertEquals(t2.email, "test2@test2.com");

        assertEquals(o2.firstName, "MyName2");
        assertEquals(o2.lastName, "MyLastName2");
        assertEquals(o2.gender, Gender.FEMALE);
        assertEquals(o2.language, Language.DUTCH);
        assertEquals(o2.email, "test2@test2.com");

        assertEquals(a2.firstName, "MyName2");
        assertEquals(a2.lastName, "MyLastName2");
        assertEquals(a2.gender, Gender.FEMALE);
        assertEquals(a2.language, Language.DUTCH);
        assertEquals(a2.email, "test2@test2.com");
    }

    /**
     * Testing of editProfiles for all roles.
     */
    @Test
    public void testProfiles(){
        Pupil p = new Pupil("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH",1,1,1998);
        p.save();
        Teacher t = new Teacher("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH","02552");
        t.save();
        Organizer o = new Organizer("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH");
        o.save();
        Admin a = new Admin("test@test.com", "MyName", "MyLastName", "MALE", "ENGLISH");
        a.save();
        String id1 = p.bebrasId;
        String id2 = t.bebrasId;
        String id3 = o.bebrasId;
        String id4 = a.bebrasId;

        Result result1 = callAction(controllers.routes.ref.ProfilesController.seeProfile(),fakeRequest().withSession("bebrasId", id1).withSession("role", "pupil"));
        assertEquals(200,status(result1));
        assertTrue(contentAsString(result1).contains(p.firstName));
        assertTrue(contentAsString(result1).contains(p.lastName));

        Result result2 = callAction(controllers.routes.ref.ProfilesController.seeProfile(),fakeRequest().withSession("bebrasId", id2).withSession("role", "teacher"));
        assertEquals(200,status(result2));
        assertTrue(contentAsString(result2).contains(t.firstName));
        assertTrue(contentAsString(result2).contains(t.lastName));

        Result result3 = callAction(controllers.routes.ref.ProfilesController.seeProfile(),fakeRequest().withSession("bebrasId", id3).withSession("role", "organizer"));
        assertEquals(200,status(result3));
        assertTrue(contentAsString(result1).contains(o.firstName));
        assertTrue(contentAsString(result1).contains(o.lastName));

        Result result4 = callAction(controllers.routes.ref.ProfilesController.seeProfile(),fakeRequest().withSession("bebrasId", id4).withSession("role", "admin"));
        assertEquals(200,status(result4));
        assertTrue(contentAsString(result1).contains(a.firstName));
        assertTrue(contentAsString(result1).contains(a.lastName));


    }

}