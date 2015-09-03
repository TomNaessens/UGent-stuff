package controllers;

import com.avaje.ebean.Ebean;
import models.*;
import models.Class;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.joda.time.DateTime;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;
import static org.junit.Assert.*;

import java.io.*;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static play.mvc.Http.HeaderNames.CONTENT_LANGUAGE;
import static play.test.Helpers.*;
import static play.test.Helpers.fakeRequest;
import static play.test.Helpers.status;

/**
 * Test class for the WriteInfoToFIle and WriteResultsToFile controllers
 */
public class WriteToFileTest extends WithApplication {

    private Class cl;
    private Competition competition;
    private Set set;


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
        Ebean.save(all.get("sets"));

       /*Preparing history of student*/

       Pupil p = Pupil.getPupil("tvanregenmortel");
       cl = p.currentClass;


        Question q = new Question("author", AnswerType.MULTIPLE_CHOICE, "A", null, null);
        q.save();
        Question q2 = new Question("author", AnswerType.MULTIPLE_CHOICE, "B", null, null);
        q.save();
        Question q3 = new Question("author", AnswerType.MULTIPLE_CHOICE, "C", null, null);
        q.save();
        set = new Set(120, false, "WOOKIE", CompetitionType.LOCAL, new Set_Language("test", Language.ENGLISH));
        set.save();

        competition = Competition.createCompetition(
                new Competition_Language("competition", Language.DUTCH),
                CompetitionType.LOCAL);
        competition.save();

        ParticipationHistory history = new ParticipationHistory(p, competition, set,
                DateTime.now().minus(60000), DateTime.now());
        history.save();

        Set_Question sq = new Set_Question(Difficulties.HARD,(short)50,(short)10,q, set);
        sq.save();
        Set_Question sq1 = new Set_Question(Difficulties.AVERAGE,(short)40,(short)10,q2, set);
        sq1.save();
        Set_Question sq2 = new Set_Question(Difficulties.EASY,(short)30,(short)10,q3, set);
        sq2.save();
        AnswerHistory ahistory = new AnswerHistory(history, q, "B");
        ahistory.save();
        AnswerHistory ahistory2 = new AnswerHistory(history, q2, "B");
        ahistory2.save();
        AnswerHistory ahistory3 = new AnswerHistory(history, q3, "C");
        ahistory3.save();
    }

    @Test
    public void resultsToCsv(){
        WriteResultsToFile writeObject = new WriteResultsToFile();
        String file = writeObject.resultsToCsv(cl, competition, set, Language.DUTCH);
        assertTrue(file.length() > 0);
        FileWriter fileOut = null;
        /*For testing with real file, uncomment and fill in correct path
        try {
            fileOut = new FileWriter("C:/Users/../test.csv",true);
            fileOut.write(file);
            fileOut.flush();
        } catch (IOException e) {
            System.err.println("Problem with writing csv file");
        }
        */

    }



    @Test
    public void resultToXls(){
        WriteResultsToFile writeObject = new WriteResultsToFile();
        Workbook workbook = new HSSFWorkbook();
        Workbook result = writeObject.resultsToexcel(cl, competition, set, workbook, Language.DUTCH);
        assertNotNull(result);
    }

    @Test
    public void resultToXlsx(){
        WriteResultsToFile writeObject = new WriteResultsToFile();
        Workbook workbook = new XSSFWorkbook();
        Workbook result =writeObject.resultsToexcel(cl, competition, set, workbook, Language.DUTCH);
        assertNotNull(result);
    }

    @Test
    public void testDownloadSchoolClassexcel(){
        WriteInfoToFile cl = new WriteInfoToFile();

        Workbook workbook1 = new HSSFWorkbook();
        Workbook workbook2 = new HSSFWorkbook();
        Workbook workbook3 = new XSSFWorkbook();
        Workbook workbook4 = new XSSFWorkbook();
        Class myClass = Class.find.all().get(0);
        School mySchool = School.find.all().get(0);
        workbook1 = cl.writeClassToexcel(myClass, workbook1, false);
        workbook2 = cl.writeSchoolToexcel(mySchool, workbook2, true);
        workbook3 = cl.writeClassToexcel(myClass, workbook3, false);
        workbook4 = cl.writeSchoolToexcel(mySchool, workbook4, true);

        assertNotNull(workbook1);
        assertNotNull(workbook2);
        assertNotNull(workbook3);
        assertNotNull(workbook4);

        /*FOR TESTING downloaded file: uncomment and fill in next lines
        try (OutputStream output = new BufferedOutputStream(new FileOutputStream("C:/Users/../test.xlsx"))){
            workbook4.write(output);
        }catch(IOException ex) {
        }
        try (OutputStream output = new BufferedOutputStream(new FileOutputStream("C:/Users/../test.xls"))){
            workbook2.write(output);
        }catch(IOException ex) {
        }
        */

    }

    @Test
    public void testPageDownloadClasses(){
        Teacher t = Teacher.getTeacher("hswimberghe");
        final School sch = Class.findClassesByTeacher(t).get(0).school;
        Map<String, String> map1 = new HashMap<String, String>() {
            {
                put("Year", "CURRENT");
                put("School", (sch.id).toString());
                put("Type", "CSV");
            }
        };
        Result result1 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map1));
        assertEquals(200,status(result1));

        Map<String, String> map2 = new HashMap<String, String>() {
            {
                put("Year", "PREVIOUS");
                put("School",(sch.id).toString() );
                put("Type", "CSV");
            }
        };
        Result result2 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map2));
        assertEquals(200,status(result2));

        Map<String, String> map3 = new HashMap<String, String>() {
            {
                put("Year", "CURRENT");
                put("School",(sch.id).toString() );
                put("Type", "XLS");
            }
        };
        Result result3 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map3));
        assertEquals(200,status(result3));

        Map<String, String> map4 = new HashMap<String, String>() {
            {
                put("Year", "PREVIOUS");
                put("School",(sch.id).toString() );
                put("Type", "XLS");
            }
        };
        Result result4 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map4));
        assertEquals(200,status(result4));

        Map<String, String> map5 = new HashMap<String, String>() {
            {
                put("Year", "CURRENT");
                put("School",(sch.id).toString() );
                put("Type", "XLSX");
            }
        };
        Result result5 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map5));
        assertEquals(200,status(result5));

        Map<String, String> map6 = new HashMap<String, String>() {
            {
                put("Year", "PREVIOUS");
                put("School",(sch.id).toString() );
                put("Type", "XLSX");
            }
        };
        Result result6 = callAction(controllers.routes.ref.WriteInfoToFile.downloadClasses(),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher")
                .withFormUrlEncodedBody(map6));
        assertEquals(200,status(result6));
    }

    @Test
    public void testPageDownloadResults(){
        Teacher t = Teacher.getTeacher("hswimberghe");
        Class cl = Class.findClassesByTeacher(t).get(0);
        Competition cm = Competition.findAllCompetitions().get(0);
        Class_Competition.createClassCompetition(cl,  cm);
        cl.openCompetition(cm);
        cl.closeCompetition(cm);
        Result result1 = callAction(controllers.routes.ref.WriteResultsToFile.downloadResults(cm.id, cl.id,1),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher"));
        assertEquals(200,status(result1));


        Result result2 = callAction(controllers.routes.ref.WriteResultsToFile.downloadResults(cm.id, cl.id,2),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher"));
        assertEquals(200,status(result2));


        Result result3 = callAction(controllers.routes.ref.WriteResultsToFile.downloadResults(cm.id, cl.id,3),fakeRequest().withSession("bebrasId", "hwimberghe").withSession("role", "teacher"));
        assertEquals(200,status(result3));
    }


}
