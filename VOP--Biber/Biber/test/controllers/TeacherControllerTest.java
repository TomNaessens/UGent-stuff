package controllers;

import static org.junit.Assert.*;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.*;
import java.util.List;
import java.util.Map;

import models.Person;
import models.Pupil;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;
import com.avaje.ebean.validation.AssertTrue;
import com.google.common.collect.ImmutableMap;

import play.libs.Yaml;
import play.mvc.Http.Cookie;
import play.mvc.Result;
import play.test.Helpers;
import play.test.WithApplication;
import utils.Hash;

/**
 * Test class for some functions of the teacher role
 *      Tested: addClassToSchool
 *              addExistingPupilToClass
 */
public class TeacherControllerTest extends WithApplication {

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        // Because yaml doesn't uses default empty constructor
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            person.firstPassword = "";
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
    }
    
    /**
     * Test the action for adding a class to a school.
     */
    @Test
    public void testAddClassToSchool(){
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303,status(result));
        Cookie cookie = play.test.Helpers.cookie("PLAY_SESSION",result);
        Teacher t = Teacher.getTeacher("hswimberghe");
        int amountOfClassesOfTeacher = models.Class.findClassesByTeacher(t).size();

        String school = t.schools.get(0).id + " - " + t.schools.get(0).name;
        result = callAction(
                controllers.routes.ref.TeacherController.addClassToSchool(school, "1a" , "WOOKIE"),fakeRequest().withCookies(cookie));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("1a"));
        assertTrue(models.Class.findClassesByTeacher(t).size() > amountOfClassesOfTeacher);
    }
    
    /**
     * Test the json result for the correct values when adding a class already existing in this school.
     */
    @Test
    public void testAddDoubleClassToSchool(){
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303,status(result));
        
        Cookie cookie = play.test.Helpers.cookie("PLAY_SESSION",result);
        Teacher t = Teacher.getTeacher("hswimberghe");
        String school = t.schools.get(0).id + " - " + t.schools.get(0).name;
        result = callAction(
                controllers.routes.ref.TeacherController.addClassToSchool(school, "1a" , "WOOKIE"),fakeRequest().withCookies(cookie));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("1a"));
        //double adding
        result = callAction(
                controllers.routes.ref.TeacherController.addClassToSchool(school, "1a" , "WOOKIE"),fakeRequest().withCookies(cookie));
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("alreadyExists"));
    }
    
    /**
     * Test for adding an existing pupil to the given class
     */
    @Test
    public void addExistingPupilToClassTest(){
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303,status(result));
        
        Cookie cookie = play.test.Helpers.cookie("PLAY_SESSION",result);
        Teacher t = Teacher.getTeacher("hswimberghe");
        models.Class cl = models.Class.findClassesByTeacher(t).get(0);
        
        result = callAction(controllers.routes.ref.TeacherController.addExistingPupilToClass(cl.id.toString(), "jjansen"),fakeRequest().withCookies(cookie));
        
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("redirect"));
        assertEquals(Pupil.getPupil("jjansen").currentClass, cl);
    }
    
    /**
     * Test for adding a not existing bebrasId to a class
     */
    @Test
    public void addExistingPupilToClassFailed(){
        Result result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","secret")));
        assertEquals(303,status(result));
        
        Cookie cookie = play.test.Helpers.cookie("PLAY_SESSION",result);
        Teacher t = Teacher.getTeacher("hswimberghe");
        models.Class cl = models.Class.findClassesByTeacher(t).get(0);
        
        result = callAction(controllers.routes.ref.TeacherController.addExistingPupilToClass(cl.id.toString(), "xxx"),fakeRequest().withCookies(cookie));
        
        assertEquals(200, status(result));
        assertEquals(Helpers.contentType(result),"application/json");
        assertTrue(Helpers.contentAsString(result).contains("status"));
    }
    
    
    
    
}
