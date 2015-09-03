package models;

import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class AnonUserStatsTests extends WithApplication{

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
    }

    @Test
    public void testAnonymous(){
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

        Set s1 = new Set(50, false, "WOOKIE", CompetitionType.LOCAL,new Set_Language("test", Language.ENGLISH));
        s1.save();

        Anonymous_User_Stats aStats = new Anonymous_User_Stats(question, s1);
        aStats.save();
        assertEquals(aStats.numberCorrect,0);
        assertEquals(aStats.numberWrong,0);
        aStats.incrementCorrect();
        assertEquals(aStats.numberCorrect,1);
        aStats.incrementCorrect();
        aStats.incrementWrong();
        aStats.decrementCorrect();
        aStats.decrementWrong();
        aStats.incrementWrong();
        assertEquals(aStats.numberWrong, 1);
        assertEquals(aStats.numberCorrect, 1);
        aStats.save();

        Anonymous_User_Stats test = Anonymous_User_Stats.findAnonymousStats(question, s1);
        assertEquals(aStats.numberCorrect, test.numberCorrect);
        assertEquals(aStats.numberWrong, test.numberWrong);

    }

}
