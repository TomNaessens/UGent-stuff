package controllers;

import models.Person;
import models.Teacher;
import static org.junit.Assert.*;
import java.util.*;

import org.junit.Before;
import org.junit.Test;

import play.mvc.*;
import play.mvc.Http.Cookie;
import play.test.WithApplication;
import play.libs.*;
import utils.Hash;
import static play.test.Helpers.*;
import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;

/**
 * Test class for the login functionality
 */
public class LoginTest extends WithApplication{
    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String,List<Object>> all = (Map<String,List<Object>>)Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>)(Object)all.get("persons");
        //Because yaml doesn't uses default empty constructor
        for(Person person: persons){
            person.password = Hash.createPassword("secret");
            //This is logintest, so assume that account is already activated by setting firstpassword to empty string
            person.firstPassword = "";
            Ebean.save(person);
            if(person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
            }
    }
    
    
    /*
     * Testing authentication for every role. 303 Status Code means that auth succeded and user gets redirected
     */
    @org.junit.Test
    public void authenticateSuccess() {
        //Teacher
        Result result = callAction(
            controllers.routes.ref.Application.authenticate(),
            fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                "bebrasId", "hswimberghe",
                "password", "secret"))
        );
        
        assertEquals(303, status(result));
        assertEquals("hswimberghe", session(result).get("bebrasId"));
        assertEquals("teacher", session(result).get("role"));
        
        //Pupil
        Result result2 = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                    "bebrasId", "tvanregenmortel",
                    "password", "secret"))
            );
        assertEquals(303, status(result2));
        assertEquals("tvanregenmortel", session(result2).get("bebrasId"));
        assertEquals("pupil", session(result2).get("role"));
        
        //Organizer
        Result result3 = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                    "bebrasId", "ebral",
                    "password", "secret"))
            );
            assertEquals(303, status(result));
            assertEquals("ebral", session(result3).get("bebrasId"));
            assertEquals("organizer", session(result3).get("role"));
            
        //Admin
            Result result4 = callAction(
                    controllers.routes.ref.Application.authenticate(),
                    fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                        "bebrasId", "nkrohn",
                        "password", "secret"))
                );
                assertEquals(303, status(result4));
                assertEquals("nkrohn", session(result4).get("bebrasId"));
                assertEquals("admin", session(result4).get("role"));
    }

    
    /*
     * Testing authentication with bad and empty usernames/password for different roles. All 4 should fail
     */
    @org.junit.Test
    public void authenticateFailure(){
      //Teacher
        Result result = callAction(
            controllers.routes.ref.Application.authenticate(),
            fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                "bebrasId", "hswimberghe",
                "password", "fout"))
        );
        assertEquals(400, status(result));
        assertNull(session(result).get("bebrasId"));
        assertNull(session(result).get("role"));
        
        //Pupil
        Result result2 = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                    "bebrasId", "",
                    "password", "secret"))
            );
        assertEquals(400, status(result2));
        assertNull(session(result2).get("bebrasId"));
        
        //Organizer
        Result result3 = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                    "bebrasId", "ebral",
                    "password", ""))
            );
            assertEquals(400, status(result));
            assertNull(session(result3).get("bebrasId"));
            assertNull(session(result3).get("role"));
            
        //Admin
            Result result4 = callAction(
                    controllers.routes.ref.Application.authenticate(),
                    fakeRequest().withFormUrlEncodedBody(ImmutableMap.of(
                        "bebrasId", "nkrohn",
                        "password", "hallo"))
                );
                assertEquals(400, status(result4));
                assertNull(session(result4).get("bebrasId"));
                assertNull(session(result4).get("role")); 
    }
    
    @Test
    public void logoutTest(){
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "nkrohn", "password",
                                "secret")));

        Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        result = callAction(controllers.routes.ref.Application.logout(),fakeRequest().withCookies(playSession));
        assertNull(session(result).get("bebrasId"));
        assertNull(session(result).get("role"));
        
    }

}
