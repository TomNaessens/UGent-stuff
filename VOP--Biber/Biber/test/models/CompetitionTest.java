package models;

import java.util.List;

import models.*;
import org.junit.*;
import static org.junit.Assert.*;
import play.test.WithApplication;
import views.html.createCompetition;
import static play.test.Helpers.*;

/**
 * TODO:
 *      fix test for getNotParticipatingClasses()
 */
public class CompetitionTest extends WithApplication {
    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
    }
    
    @Test
    public void createAndRetrieve(){
    	Competition local = Competition.createCompetition(
                new Competition_Language("Local", Language.ENGLISH),
                CompetitionType.LOCAL);
    	local.save();
    	
    	Competition unrestricted = Competition.createCompetition(
                new Competition_Language("Unrestricted", Language.ENGLISH),
                CompetitionType.UNRESTRICTED);
    	unrestricted.save();
    	
    	Competition official = Competition.createCompetition(
                new Competition_Language("Official", Language.ENGLISH),
                CompetitionType.OFFICIAL);
    	official.save();
    	
    	List<Competition> results = Competition.find.all();
    	assertEquals(3, results.size());
    	
    	Competition comp = Competition.findById(local.id);
    	assertEquals(local.getTitle(Language.ENGLISH), comp.getTitle(Language.ENGLISH));
    	
    }
    
    @Test
    public void retrieveUnrestrictedComps(){
    	Competition unrestricted = Competition.createCompetition(
                new Competition_Language("Unrestricted", Language.ENGLISH),
                CompetitionType.UNRESTRICTED);
    	unrestricted.save();
    	
    	Competition local = Competition.createCompetition(
                new Competition_Language("Local", Language.ENGLISH),
                CompetitionType.LOCAL);
    	local.save();
    	
    	List<Competition> results = Competition.getUnrestrictedQuizzes();
    	assertEquals(1, results.size());
    	
    }
    
    @Test
    public void retrieveParticipatingClasses(){
    	Teacher t = new Teacher("t@gmail.com", "Tom", "Van", "MALE", "DUTCH","05222");
    	Teacher t2 = new Teacher("bla","bla","bla","FEMALE","DUTCH","055520");
    	t.save();
    	t2.save();
    	
    	Competition c1 = Competition.createCompetition(
                new Competition_Language("compo 1", Language.ENGLISH),
                CompetitionType.LOCAL);
    	Competition c2 = Competition.createCompetition(
                new Competition_Language("compo 2", Language.ENGLISH),
                CompetitionType.LOCAL);
    	
    	c1.save();
    	c2.save();
    	

    	Class class1 = Class.createClass("class1", "Wookie",2012, null, t);
    	Class class2 = Class.createClass("class2","Wookie",2012,null,t);
    	Class class3 = Class.createClass("class3","Wookie",2012,null,t2);

    	
    	class1.addCompetition(c1);
    	class1.addCompetition(c2);
    	class1.openCompetition(c1);
    	class1.openCompetition(c2);

    	class2.addCompetition(c1);
    	class2.addCompetition(c2);
    	class2.openCompetition(c1);
    	
    	class3.addCompetition(c1);
    	class3.addCompetition(c2);
    	class3.openCompetition(c1);
    	
    	class1.save();class2.save();class3.save();
    	
    	Class.createClass("class3", "Wookie", 2012, null, t);
    	
    	List<Class> classes_c1 = c1.getParticipatingClasses(t.bebrasId);
    	assertEquals(2,classes_c1.size());
    	List<Class> classes_c2 = c2.getParticipatingClasses(t.bebrasId);
    	assertEquals(1,classes_c2.size());
    	assertEquals("class1",Class.find.where().eq("id",classes_c2.get(0).id).findUnique().name);  

    	List<Class> classes = c2.getNotParticipatingClasses(t.bebrasId);
    	assertEquals(2,classes.size());
    	assertEquals("class2",Class.find.where().eq("id",classes.get(0).id).findUnique().name);

    	
    }
    
    @Test
    public void openCompetitionForClass(){
    	Class c = Class.createClass("1a", "Wookie",2012, null, null);
    	Competition compo = Competition.createCompetition(
                new Competition_Language("test", Language.ENGLISH),
                CompetitionType.LOCAL);
    	c.addCompetition(compo);
    	
    	assertEquals(1, c.getAvailableCompetitions().size());
    	c.openCompetition(compo);
    	Class_Competition cc = Class_Competition.find.where().eq("currentClass.id",c.id).eq("competition.id", compo.id).findUnique();
    	
    	assertNotNull(cc);
    	assertEquals(1,cc.isOpen);
    	
    	List<Class_Competition> lcc = Class_Competition.find.all();
    	assertEquals(1,lcc.size());
    	
    	Class c2 = Class.find.where().eq("id", c.id).findUnique();
    	assertEquals(1,Class_Competition.getClassCompetitions(c2).get(0).isOpen);
    	
    }
    
    @Test
    public void addQuestionSets(){
    	Set s1 = new Set(50, false, "WOOKIE", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
    	Set s2 = new Set(50, false, "EWOK", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
    	Set s3 = new Set(50, false, "PADAWAN", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
    	Set s4 = new Set(50, false, "JEDI", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
    	Set s5 = new Set(50, false, "WOOKIE", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
    	
    	Competition c1 = Competition.createCompetition(new Competition_Language("test1", Language.ENGLISH), CompetitionType.LOCAL);
    	Competition c2 = Competition.createCompetition(new Competition_Language("test2", Language.ENGLISH), CompetitionType.LOCAL);
    	Competition c3 = Competition.createCompetition(new Competition_Language("test3", Language.ENGLISH), CompetitionType.LOCAL);
    	
    	Set[] test1 = {s1,s2};
    	Set[] test2 = {s1,s2,s3,s4,s5};
    	Set[] test3 = {s1,s5};
    	Set[] test4 = {s3,s5};
    	
    	assertEquals(true, c1.addQuestionSets(test1));
    	assertEquals(false, c2.addQuestionSets(test2));
    	assertEquals(false, c3.addQuestionSets(test3));
    	assertEquals(false, c1.addQuestionSets(test2));
    	
    	assertEquals(2,Competition.find.where().eq("competitionLanguages.title","test1").findUnique().questionSets.size());
    	assertEquals(0,Competition.find.where().eq("competitionLanguages.title","test2").findUnique().questionSets.size());
    	assertEquals(1,Competition.find.where().eq("competitionLanguages.title","test3").findUnique().questionSets.size());
    	
    	assertEquals(false, c1.addQuestionSets(test4));
    	assertEquals(3,Competition.find.where().eq("competitionLanguages.title","test1").findUnique().questionSets.size());
    	
    	
    }
    
    @Test
    public void ToggleUnrestrictedCompetition() {
    	Set_Language settitle = new Set_Language("Test", Language.ENGLISH);
    	Competition_Language comptitle = new Competition_Language("Test", Language.ENGLISH);
    	
    	Set set1 = new Set(3600,false,"WOOKIE",CompetitionType.UNRESTRICTED,settitle);
    	Set set2 = new Set(3600,false,"WOOKIE",CompetitionType.OFFICIAL,settitle);
    	Competition comp1 = Competition.createUnrestrictedCompetition(set1);
    	Competition.toggleUnrestrictedCompetition(set1);
    	Competition testcomp1 = Competition.getUnrestrictedCompetitionForSet(set1);
    	assertNotNull(testcomp1);
    	assertEquals(comp1.id, testcomp1.id);
    	assertEquals(Competition.VISIBLE,testcomp1.isOpen);
    	
    	Competition testcomp2 = Competition.getUnrestrictedCompetitionForSet(set2);
    	assertNull(testcomp2);
    	
    	testcomp2 = Competition.createUnrestrictedCompetition(set2);
    	Competition.toggleUnrestrictedCompetition(set2);
    	testcomp2 = Competition.getUnrestrictedCompetitionForSet(set2);
    	assertNotNull(testcomp2);
    	assertEquals(Competition.NOTVISIBLE,testcomp2.isOpen);
    }
    
    
    
}