package models;

import static org.junit.Assert.*;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;

import play.libs.Yaml;
import play.test.WithApplication;
import utils.Hash;

public class TokenTest extends WithApplication{

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            person.firstPassword = "";
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
    }
    
    /**
     * Create a token, send it to the database and retrieve it.
     */
    @Test
    public void createAndRetrieveToken(){
        Person teach = Teacher.getTeacher("hswimberghe");
        Token token = Token.createNewToken(teach ,null);
        String tokenString = token.token;
        Token retrievedToken = Token.findByToken(tokenString);
        assertNotNull(retrievedToken);   
    }
    
    /**
     * Test if isExpired() works as expected.
     */
    @Test
    public void testTokenExpired(){
        Person teach = Teacher.getTeacher("hswimberghe");
        Token token = Token.createNewToken(teach ,null);
        token.dateOfCreation = token.dateOfCreation.minusMinutes(5);
        assertFalse(token.isExpired());
        token.dateOfCreation = token.dateOfCreation.minusDays(1);
        assertTrue(token.isExpired());
    }
    
    
}
