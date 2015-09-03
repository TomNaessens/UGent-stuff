import models.Set_Question;
import play.*;
import play.libs.*;
import utils.Hash;
import models.*;
import models.Set;

import com.avaje.ebean.Ebean;

import java.lang.Long;
import java.lang.Object;
import java.util.*;

import org.joda.time.DateTime;

public class Global extends GlobalSettings {
    @Override
    public void onStart(Application app) {

        // Check if the database is empty
        if (Teacher.find.findRowCount() == 0) {
            Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");

            //Save Competitions
            Ebean.save(all.get("competitions"));
            //Load schools 
            Ebean.save(all.get("schools"));
            //Load sets
            Ebean.save(all.get("sets"));
            //Load fileservers
            Ebean.save(all.get("fileservers"));

            // Load persons from test-data file
            List<Person> persons = (List<Person>) (Object) all.get("persons");
            for (Person p : persons) {
                if (Play.isProd()) {
                    p.firstPassword = "secret";
                } else {
                	 p.firstPassword = "";
                }
                if(p instanceof Pupil){
                    ((Pupil)p).dateOfBirth = DateTime.now();
                    ((Pupil)p).deactivated = false;
                }
                p.password = Hash.createPassword("secret");
                Ebean.save(p);
                if(p instanceof Teacher)
                    Ebean.saveManyToManyAssociations(p, "schools");
                
            }
            //For other data, see up
            Ebean.save(all.get("classes"));
            Ebean.save(all.get("questions"));
            Ebean.save(all.get("set_questions"));
            Ebean.save(all.get("class_competitions"));

        }
    }

}
