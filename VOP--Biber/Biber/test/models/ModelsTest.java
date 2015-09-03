package models;

import com.avaje.ebean.Ebean;
import org.junit.*;

import static models.School.findSchool;
import static org.junit.Assert.*;

import play.libs.Yaml;
import play.test.WithApplication;
import utils.Hash;
import utils.LangMessages;

import java.util.List;
import java.util.Map;

import static play.test.Helpers.*;


/**
 * These tests can use data provided by the test-data.yml file.
 * There are also some general tests in this class, which do not have an own specific
 * test class.
 *
 * Tested:
 *      interactions between pupil, teacher and class.
 *      Class Difficulties
 */
public class ModelsTest extends WithApplication {

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        Ebean.save(all.get("schools"));
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

    @Test
    public void testPupilFindPupilsFromClass() {
        Person p = Person.getPerson("hswimberghe");
        Teacher tc = Teacher.find.where().eq("firstName", "Hannes").findUnique();
        assertNotNull(tc);
        List<Class> lijst = Class.findClassesByTeacher(tc);
        assertTrue(lijst.size() > 0);
        assertTrue(Pupil.findPupilsFromClass(lijst.get(0)).size() > 0);
    }

    @Test
    public void testDifficulties(){
        assertTrue(Difficulties.list().contains(LangMessages.get("enum.difficulties.EASY")));
        assertTrue(Difficulties.list().contains(LangMessages.get("enum.difficulties.AVERAGE")));
        assertTrue(Difficulties.list().contains(LangMessages.get("enum.difficulties.HARD")));
    }




}