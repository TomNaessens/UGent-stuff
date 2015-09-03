package controllers;
import static org.junit.Assert.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.status;
import static play.test.Helpers.session;


import java.util.List;
import java.util.Map;

import models.Language;
import models.Person;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;

import play.libs.Yaml;
import play.mvc.Result;
import play.mvc.Http.Cookie;
import play.test.Helpers;
import play.test.WithApplication;
import utils.Hash;

/**
 * Test class for the mimick user functionality
 */
public class MimickUserTest extends WithApplication{

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
     * Test admin mimicking and stop mimicking organizer, pupil and teacher.
     */
    @Test
    public void testAdminMimick(){
        Result result = callAction(
                controllers.routes.ref.Application.mimickUser("hswimberghe"),fakeRequest().withSession("bebrasId", "nkrohn").withSession("language", Language.ENGLISH.name()).withSession("role", "admin"));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertEquals("hswimberghe",session(result).get("bebrasId"));
        assertEquals("teacher",session(result).get("role"));
        
        Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(controllers.routes.ref.Application.stopMimick(),fakeRequest().withCookies(playSession));
        assertEquals(303, status(result));
        assertEquals("nkrohn",session(result).get("bebrasId"));
        assertEquals("admin",session(result).get("role"));

        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(controllers.routes.ref.Application.mimickUser("tvanregenmortel"),fakeRequest().withCookies(playSession));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertEquals("tvanregenmortel",session(result).get("bebrasId"));
        assertEquals("pupil",session(result).get("role"));
        
        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);

        result = callAction(controllers.routes.ref.Application.stopMimick(),fakeRequest().withCookies(playSession));
        assertEquals(303, status(result));
        assertEquals("nkrohn",session(result).get("bebrasId"));
        assertEquals("admin",session(result).get("role"));
        
        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);

        result = callAction(controllers.routes.ref.Application.mimickUser("ebral"),fakeRequest().withCookies(playSession));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertEquals("ebral",session(result).get("bebrasId"));
        assertEquals("organizer",session(result).get("role"));
        
        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        result = callAction(controllers.routes.ref.Application.logout(), fakeRequest().withCookies(playSession));
        
        assertNull(session(result).get("bebrasId"));
        assertNull(session(result).get("role"));
        assertNull(session(result).get("mimickId"));
        assertNull(session(result).get("mimickRole"));
    }
    
    /**
     * Test mimicking for organizer.
     */
    @Test
    public void testOrganizerMimick(){
        Result result = callAction(
                controllers.routes.ref.Application.mimickUser("hswimberghe"), fakeRequest().withSession("bebrasId", "ebral").withSession("language", Language.ENGLISH.name()).withSession("role", "organizer"));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");

        assertEquals("hswimberghe",session(result).get("bebrasId"));
        assertEquals("teacher",session(result).get("role"));
        
        Cookie playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(controllers.routes.ref.Application.stopMimick(),fakeRequest().withCookies(playSession));
        assertEquals(303, status(result));

        assertEquals("ebral",session(result).get("bebrasId"));
        assertEquals("organizer",session(result).get("role"));
        
        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
        
        result = callAction(controllers.routes.ref.Application.mimickUser("tvanregenmortel"),fakeRequest().withCookies(playSession));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("not authorized"));
        
        playSession = play.test.Helpers.cookie("PLAY_SESSION",result);
    }
    
    /**
     * Test mimicking when not authorized
     */
    @Test
    public void testNotAuthorizedMimick(){
        Result result = callAction(
                controllers.routes.ref.Application.mimickUser("tvanregenmortel"), fakeRequest().withSession("bebrasId", "ebral").withSession("language", Language.ENGLISH.name()).withSession("role", "organizer"));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("not authorized"));
        
        assertEquals("ebral",session(result).get("bebrasId"));
        assertEquals("organizer",session(result).get("role"));
    }
    
    /**
     * Test mimicking for a not existing bebrasId
     */
    @Test
    public void testNotExistingId(){ //TODO: this test only succeeds when session("role", currentRole) is executed in the if in the controller 
        Result result = callAction(
                controllers.routes.ref.Application.mimickUser("xxx"),fakeRequest().withSession("bebrasId", "ebral").withSession("language", Language.ENGLISH.name()).withSession("role", "organizer"));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("not exist"));
        
        assertEquals("ebral",session(result).get("bebrasId"));
        assertEquals("organizer",session(result).get("role"));
    }
    
}
