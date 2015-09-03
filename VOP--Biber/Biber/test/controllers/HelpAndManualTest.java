package controllers;

import com.avaje.ebean.Ebean;
import models.Language;
import models.Person;
import models.Teacher;
import org.junit.Before;
import org.junit.Test;
import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.*;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class HelpAndManualTest extends WithApplication {
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
     * Test for the renderHelpPage method in the ProfilesController class.
     */
    @Test
    public void testHelpPages(){
        Result result1 = callAction(controllers.routes.ref.ProfilesController.renderHelpPage(),fakeRequest().withSession("bebrasId", "tvanregenmortel").withSession("role", "pupil"));
        assertEquals(200,status(result1));
        assertTrue(contentAsString(result1).contains("Pupil"));

        Result result2 = callAction(controllers.routes.ref.ProfilesController.renderHelpPage(),fakeRequest().withSession("bebrasId", "hswimberghe").withSession("role", "teacher"));
        assertEquals(200,status(result2));
        assertTrue(contentAsString(result2).contains("Teacher"));

        Result result3 = callAction(controllers.routes.ref.ProfilesController.renderHelpPage(),fakeRequest().withSession("bebrasId", "ebral").withSession("role", "organizer"));
        assertEquals(200,status(result3));
        assertTrue(contentAsString(result3).contains("Organizer"));

        Result result4 = callAction(controllers.routes.ref.ProfilesController.renderHelpPage(),fakeRequest().withSession("bebrasId", "nkrohn").withSession("role", "admin"));
        assertEquals(200,status(result4));
        assertTrue(contentAsString(result4).contains("Admin"));
    }

    /**
     *
     */
    @Test
    public void testDownloadManuals(){
        //Language DUTCH
        Result result1 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "tvanregenmortel").withSession("role", "pupil").withSession("language",Language.DUTCH.name()));
        assertEquals(303, status(result1));

        Result result2 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "hswimberghe").withSession("role", "teacher").withSession("language",Language.DUTCH.name()));
        assertEquals(303, status(result2));

        Result result3 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "ebral").withSession("role", "organizer").withSession("language",Language.DUTCH.name()));
        assertEquals(303, status(result3));

        Result result4 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "nkrohn").withSession("role", "admin").withSession("language",Language.DUTCH.name()));
        assertEquals(303,status(result4));

        //Language ENGLISH
        Result result21 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "tvanregenmortel").withSession("role", "pupil").withSession("language",Language.ENGLISH.name()));
        assertEquals(303, status(result21));

        Result result22 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "hswimberghe").withSession("role", "teacher").withSession("language",Language.ENGLISH.name()));
        assertEquals(303, status(result22));

        Result result23 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "ebral").withSession("role", "organizer").withSession("language",Language.ENGLISH.name()));
        assertEquals(303, status(result23));

        Result result24 = callAction(controllers.routes.ref.ProfilesController.downloadManual(),fakeRequest().withSession("bebrasId", "nkrohn").withSession("role", "admin").withSession("language",Language.ENGLISH.name()));
        assertEquals(303,status(result24));
    }
}
