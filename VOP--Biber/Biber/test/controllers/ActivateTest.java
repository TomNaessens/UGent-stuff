package controllers;

import static org.junit.Assert.assertEquals;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.session;
import static play.test.Helpers.status;


import java.util.List;
import java.util.Map;

import models.Person;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;

import play.libs.Yaml;
import play.mvc.Result;
import play.mvc.Http.Cookie;
import play.test.WithApplication;
import utils.Hash;

/**
 * Test class for the activate account functionality
 */
public class ActivateTest extends WithApplication {
    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        // Because yaml doesn't uses default empty constructor
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            person.firstPassword = "secret";
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
    }

    /**
     * Testing activating (and logging in with new password) for some roles. 303 Status Code means that activation
     * succeeded and user gets redirected.
     */
    @Test
    public void ActivateSucces() {
        // Teacher
        //First login
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303, status(result));
        
        //Keep cookie for next call
        final Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        //Activate
        result = callAction(
                controllers.routes.ref.Application.activate(),
                fakeRequest().withCookies(playSession).withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "newPassword","hannes","confirmNewPassword","hannes")));
        assertEquals(303, status(result));
        
        //Login with new password
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","hannes")));
        assertEquals(303, status(result));
        assertEquals("hswimberghe", session(result).get("bebrasId"));
        assertEquals("teacher", session(result).get("role"));
        
        // Pupil
        
      //First login
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "tvanregenmortel", "password","secret")));
        assertEquals(303, status(result));
        
        //Keep cookie for next call
        final Cookie playSession2 = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(
                controllers.routes.ref.Application.activate(),
                fakeRequest().withCookies(playSession2).withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "tvanregenmortel", "newPassword","tom","confirmNewPassword","tom")));
        assertEquals(303, status(result));
        
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "tvanregenmortel", "password","tom")));
        assertEquals(303, status(result));
        assertEquals("tvanregenmortel", session(result).get("bebrasId"));
        assertEquals("pupil", session(result).get("role"));            
    }
    
    /**
     * Testing failed activating using not equal passwords in the form. 400 Status Code means that activation failed
     */
    @Test
    public void ActivateFail(){
        //First login
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303, status(result));
        
        //Keep cookie for next call
        final Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(
                controllers.routes.ref.Application.activate(),
                fakeRequest().withCookies(playSession).withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "newPassword","hannes","confirmNewPassword","hannes2")));
        assertEquals(400, status(result)); 
    }
    
    
    /**
     * Security test by trying to activate an account without succesfully logging in for the first time. Should return a 403!
     */
    @Test
    public void ActivateWithoutFirstLogin(){
        Result result = callAction(
                controllers.routes.ref.Application.activate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "newPassword","hannes","confirmNewPassword","hannes2")));
        assertEquals(403, status(result)); 
    }

}
