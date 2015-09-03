package models;


import org.joda.time.DateTime;
import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

public class ParticipationHistoryTest extends WithApplication {


    /**
     * TESTS OF CLASS PARTICIPATIONHISTORY
     * <p/>
     * Tested interaction with history and set
     * <p/>
     * Methods tested:
     *      Constructor()
     *      find where set
     *      getTotalPoints()
     *
     * TODO:
     * getHistoryWithUnfinishedCompetitionFor()
     * getHistoryFor()
     * finish()
     * getTotalTime()
     * getTimeLeft()
     */

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
    }

    @Test
    public void testHistory() {
        Pupil pupil = new Pupil("mijnEmail2@internet.com", "This_is", "My_name", "MALE", "DUTCH", 1, 1, 2000);
        pupil.save();

        Question q = new Question("author", AnswerType.MULTIPLE_CHOICE, "A", null, null);
        q.save();
        Question q2 = new Question("author", AnswerType.MULTIPLE_CHOICE, "B", null, null);
        q.save();
        Question q3 = new Question("author", AnswerType.MULTIPLE_CHOICE, "C", null, null);
        q.save();
        Set set = new Set(120, false, "WOOKIE", CompetitionType.LOCAL, new Set_Language("test", Language.ENGLISH));
        set.save();


        Competition competition = Competition.createCompetition(
                new Competition_Language("competition", Language.DUTCH),
                CompetitionType.LOCAL);
        competition.save();

        ParticipationHistory history = new ParticipationHistory(pupil, competition, set,
                DateTime.now().minus(60000), DateTime.now());
        history.save();


        assertTrue(ParticipationHistory.find.where().eq("questionSet", set).findList().size() > 0);


        /*Test for method getTotalPoints*/
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

        assertEquals(history.getTotalPoints(), set.getInitialPoints()+40+30-10);
    }

}
