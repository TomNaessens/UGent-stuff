package controllers;

import com.avaje.ebean.Ebean;
import com.google.common.collect.ImmutableMap;
import models.*;
import models.Class;
import org.joda.time.DateTime;
import org.junit.Before;
import org.junit.Test;
import play.libs.Yaml;
import play.mvc.Result;
import play.test.WithApplication;
import utils.Hash;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static junit.framework.Assert.*;
import static play.test.Helpers.*;

/**
 * Created with IntelliJ IDEA.
 * User: enver
 * Date: 04/05/13
 * Time: 15:04
 * To change this template use File | Settings | File Templates.
 */
public class MonitorCompetitionTest extends WithApplication {
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
        Ebean.save(all.get("schools"));
        Ebean.save(all.get("sets"));
        Ebean.save(all.get("fileservers"));
        Ebean.save(all.get("set_questions"));
        Ebean.save(all.get("class_competitions"));

        Pupil pupil = Pupil.findPupilByBebrasID("tvanregenmortel");
        Class clazz = pupil.currentClass;

        Competition_Language cl = new Competition_Language("Local Competition", Language.ENGLISH);
        Competition competition = Competition.createCompetition(cl, CompetitionType.LOCAL);
        competition.save();

        Question_Language ql = new Question_Language("Question X", "question.html", "feedback.html", Language.ENGLISH);

        Map<Language, Question_Language> qlMap = new TreeMap<Language, Question_Language>();
        qlMap.put(Language.ENGLISH, ql);

        Question question = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", FileServer.find.byId(1l), qlMap);
        question.save();

        Set questionSet = new Set(600, false, Level.EWOK.name(), CompetitionType.LOCAL, new Set_Language("Local Question Set", Language.ENGLISH));
        questionSet.save();

        Set_Question sq = new Set_Question(Difficulties.EASY, (short)10, (short)10, question, questionSet);
        sq.save();

        competition.addQuestionSets(new Set[]{ questionSet });

        // Open competition
        Class_Competition.createClassCompetition(clazz, competition);
        Class_Competition cc = Class_Competition.findClassCompetition(competition.id, clazz.id);
        cc.isOpen = Class_Competition.OPEN;
        cc.save();

        // Start Competition
        ParticipationHistory history = new ParticipationHistory(pupil, competition, questionSet, DateTime.now());
        history.save();
    }

    @Test
    public void grantGraceTime() {
        Pupil pupil = Pupil.findPupilByBebrasID("tvanregenmortel");
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        Competition competition = history.competition;

        Map<String, String> graceTimeData = new TreeMap<String, String>();
        graceTimeData.put("time", "00:10:00");
        graceTimeData.put("pupil", pupil.bebrasId);

        // Grant grace time as teacher
        long origTimeLeft = history.getTimeLeft();
        Result result = callAction(controllers.routes.ref.MonitorCompetitionController.grantGraceTime(competition.id),
                fakeRequest()
                        .withSession("bebrasId", "hswimberghe").withSession("role", "teacher").withSession("language", Language.ENGLISH.name())
                        .withFormUrlEncodedBody(graceTimeData));
        status(result);
        history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        long currTimeLeft = history.getTimeLeft();
        assertTrue(currTimeLeft > origTimeLeft && currTimeLeft <= origTimeLeft + 10*60*1000);
    }

    @Test
    public void deleteHistory() {
        Pupil pupil = Pupil.findPupilByBebrasID("tvanregenmortel");
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        Competition competition = history.competition;

        Map<String, String> deleteHistoryData = new TreeMap<String, String>();
        deleteHistoryData.put("pupil", "tvanregenmortel");

        // Delete history as teacher
        Result result = callAction(routes.ref.MonitorCompetitionController.deleteHistory(competition.id),
                fakeRequest()
                        .withSession("bebrasId", "hswimberghe").withSession("role", "teacher").withSession("language", Language.ENGLISH.name())
                        .withFormUrlEncodedBody(deleteHistoryData));

        status(result);

        assertEquals(0, AnswerHistory.find.where().eq("history.id", history.id).findList().size());
        history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        assertNull(history);
    }

    @Test
    public void reopenCompetition() {
        Pupil pupil = Pupil.findPupilByBebrasID("tvanregenmortel");
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        Competition competition = history.competition;

        // Let pupil answer a question
        AnswerHistory answerHistory = new AnswerHistory(history, history.questionSet.getSetQuestions().get(0).question, "A");
        answerHistory.save();

        Map<String, String> reopenCompetitionData = new TreeMap<String, String>();
        reopenCompetitionData.put("pupil", "tvanregenmortel");
        reopenCompetitionData.put("time", "00:10:00");

        // Reopen competition as reacher
        Result result = callAction(routes.ref.MonitorCompetitionController.reopenCompetition(competition.id),
                fakeRequest()
                    .withSession("bebrasId", "hswimberghe").withSession("role", "teacher").withSession("language", Language.ENGLISH.name())
                    .withFormUrlEncodedBody(reopenCompetitionData)
                );
        status(result);

        history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        long currTimeLeft = history.getTimeLeft();
        assertTrue(currTimeLeft <= 10*60*1000);     // new time set to 10 minutes?

        // Answer history saved?
        AnswerHistory answerHistory2 = AnswerHistory.find.byId(answerHistory.id);
        assertNotNull(answerHistory2);
        assertEquals("A", answerHistory2.givenAnswer);
    }
}
