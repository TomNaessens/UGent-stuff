package models;


import models.*;
import org.junit.Before;
import org.junit.*;
import play.test.WithApplication;

import java.util.Map;
import java.util.TreeMap;
import static org.junit.Assert.*;

import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class SetTest extends WithApplication {
    /**
     * TESTS of CLASS SET
     * Methods tested:
     *      Constructor
     *      getSetQuestions()
     *      findSetsByLevel()
     *      findById()
     *      size()
     *      getTitle()
     *      getInitialPoints()
     *
     * TESTS of CLASS SET_QUESTION
     * Methods tested:
     *      constructor
     *      getPoints()
     *      getSet_Question()
     *
     */
    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));
    }


    @Test
    public void testSets(){
        Set s1 = new Set(50, false, "WOOKIE", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
        Set s2 = new Set(50, false, "EWOK", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
        Set s3 = new Set(50, false, "PADAWAN", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
        Set s4 = new Set(50, false, "JEDI", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
        s1.save();
        s2.save();
        s3.save();
        s4.save();

        // Setup question 1
        Map<Language, Question_Language> qls = new TreeMap<Language, Question_Language>();
        qls.put( Language.GERMAN,
                new Question_Language("biber am fluss", "question_de.html", "feedback_de.html", Language.GERMAN) );
        qls.put( Language.DUTCH,
                new Question_Language("bever aan de dam", "vraag.html", "antwoord.html", Language.DUTCH) );
        qls.put( Language.FRENCH,
                new Question_Language("castor à rivière", "question_fr.html", "feedback_fr.html", Language.FRENCH));

        Question question = new Question("eebral", AnswerType.MULTIPLE_CHOICE, "A", null, qls);
        question.save();

        Set_Question sq = new Set_Question(Difficulties.EASY, (short)50,(short)10, question, s1);
        sq.save();

        /**
         * Method getQuestions()
         */
        assertTrue(Set.getSetQuestions(s1).size()>0);

        /**
         * Method findSetsByLevel()
         */
        assertTrue(Set.findSetsByLevel(Level.WOOKIE).size()>0);
        assertTrue(Set.findSetsByLevel(Level.EWOK).size()>0);
        assertTrue(Set.findSetsByLevel(Level.PADAWAN).size()>0);
        assertTrue(Set.findSetsByLevel(Level.JEDI).size()>0);

        /**
         * Method findById()
         * */
        assertNotNull(Set.findById(s1.id));
        assertNotNull(Set.findById(s2.id));
        assertNotNull(Set.findById(s3.id));
        assertNotNull(Set.findById(s4.id));

        /**
         * Method size()
         */
        assertEquals(s1.size(), 1);

        /**
         * Method getInitialPoints()
         */
        assertTrue(s1.getInitialPoints()==10);

        /**
         * getPoints()
         */
        assertTrue(sq.getPoints("A")==50);
        assertTrue(sq.getPoints("B")==10);
        assertTrue(sq.getPoints("C")==10);
        assertTrue(sq.getPoints("D")==10);

        /**
         * Method getTitle()
         */
        assertEquals(s1.getTitle(Language.ENGLISH), "test");

        /**/
        Set_Question sq2 = new Set_Question(Difficulties.EASY, (short)100,(short)2, question, s2);
        sq.save();
        Set_Question sq3 = new Set_Question(Difficulties.EASY, (short)142,(short)8, question, s3);
        sq.save();
        Set_Question sq4 = new Set_Question(Difficulties.EASY, (short)32,(short)14, question, s4);
        sq.save();
        assertNotNull(Set_Question.getSet_Question(s1, question));
        assertNotNull(Set_Question.getSet_Question(s2, question));
        assertNotNull(Set_Question.getSet_Question(s3, question));
        assertNotNull(Set_Question.getSet_Question(s4, question));
     }


}
