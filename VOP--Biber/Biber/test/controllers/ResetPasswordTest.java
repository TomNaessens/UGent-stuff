package controllers;

import static org.junit.Assert.*;
import static org.junit.Assert.assertEquals;
import static play.test.Helpers.callAction;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.inMemoryDatabase;
import static play.test.Helpers.session;
import static play.test.Helpers.status;

import models.Token;
import java.util.List;
import java.util.Map;

import models.Class;
import models.Person;
import models.Pupil;
import models.Teacher;

import org.junit.Before;
import org.junit.Test;

import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;

import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

public class ResetPasswordTest extends WithApplication{

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            person.firstPassword = "";
            if (person.bebrasId.equals("hswimberghe")){
                person.email = "hannes.biberteam@gmail.com";
            }
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
    }
    
    @Test
    public void resetPassword(){
        Result result = callAction(
                controllers.routes.ref.Reset.askReset(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "email","")));
        assertEquals(200, status(result));
        
        Token token = Token.find.where().eq("bebrasId","hswimberghe").findUnique();
        assertNotNull(token);

        result = callAction(
                controllers.routes.ref.Reset.resetPassword(token.token),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("newPassword", "hannes",
                                "confirmNewPassword", "s")));
        assertEquals(400, status(result));
        
        result = callAction(
                controllers.routes.ref.Reset.resetPassword(token.token),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("newPassword", "hannes",
                                "confirmNewPassword", "hannes")));
        assertEquals(303, status(result));
        
        result = callAction(
                controllers.routes.ref.Application.authenticate(),
                fakeRequest().withFormUrlEncodedBody(
                        ImmutableMap.of("bebrasId", "hswimberghe", "password","hannes")));
        assertEquals(303, status(result));
        assertEquals("hswimberghe", session(result).get("bebrasId"));
        assertEquals("teacher", session(result).get("role"));
    }
    
    @Test
    public void resetPupilPassword(){
        Pupil pupil = Pupil.getPupil("tvanregenmortel");
        Result result = callAction(controllers.routes.ref.TeacherController.resetPupilPassword(pupil.bebrasId),
                fakeRequest().withSession("bebrasId", "hswimberghe").withSession("role", "teacher"));
        assertEquals(200, status(result));
        assertFalse(Pupil.getPupil("tvanregenmortel").firstPassword.equals(""));
    }
    
    
}
