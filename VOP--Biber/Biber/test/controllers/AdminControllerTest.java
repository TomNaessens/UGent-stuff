package controllers;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.status;

import java.util.List;
import java.util.Map;

import models.Organizer;
import models.Person;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import play.libs.Yaml;
import play.mvc.Http.Cookie;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;

/**
 * Test class for some functions of the admin role
 *      Tested: registerOrganizer
 */
public class AdminControllerTest extends WithApplication {
    
    
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
    }

    /**
     * Log in as an admin and register a new organizer. After that admin logs
     * out. Then new organizer logs in for the first time, needs to activate
     * account and then logs in with his new password
     */
    @Test
    public void registerOrganizerTest(){
        //Login
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "nkrohn", "password","secret")));
        
        //Keep cookie for next call
        final Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        //Register organizer
        result = callAction(controllers.routes.ref.AdminController.register_organizer(),fakeRequest().withCookies(playSession).withFormUrlEncodedBody(
                ImmutableMap.of("firstName", "Tom", "lastName","Tomsen","email","lala@gmail.com","gender","MALE","language","ENGLISH")));
        assertEquals(303, status(result));
        
        Organizer newOrganizer = Organizer.find.where().eq("bebrasId", "ttomsen").findUnique();
        assertNotNull(newOrganizer);
        
        result = callAction(controllers.routes.ref.Application.logout(),fakeRequest().withCookies(playSession));
        
        
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "ttomsen", "password",newOrganizer.firstPassword)));
        assertEquals(303, status(result));
        
        final Cookie playSession2 = play.test.Helpers.cookie("PLAY_SESSION",result);

        
        result = callAction(
                controllers.routes.ref.Application.activate(),
                fakeRequest().withCookies(playSession2).withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "ttomsen", "newPassword","tom","confirmNewPassword","tom")));
        assertEquals(303, status(result));
        
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "ttomsen", "password","tom")));
        assertEquals(303, status(result));

    }
    

}
