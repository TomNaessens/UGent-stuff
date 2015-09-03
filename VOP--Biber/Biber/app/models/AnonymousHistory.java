package models;

import models.Competition;
import models.Question;
import models.Set;
import org.joda.time.DateTime;
import org.joda.time.Duration;
import org.joda.time.Instant;
import play.db.ebean.Model;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * Holds the history for the anonymous user
 */
public class AnonymousHistory implements History {

    public Competition competition;
    public Set questionSet;
    public Map<Question, String> answerMap;

    public DateTime startTime;
    public DateTime endTime;

    public AnonymousHistory(Competition competition, Set questionSet) {
        this.competition = competition;
        this.questionSet = questionSet;

        answerMap = new TreeMap<Question, String>();
        startTime = DateTime.now();
    }

    @Override
    public Competition getCompetition() {
        return competition;
    }

    @Override
    public Set getQuestionSet() {
        return questionSet;
    }

    @Override
    public long getTimeLeft() {
        Duration duration = new Duration(
                new Instant(),
                startTime.plus(questionSet.timeLimit * 1000)
        );

        long millis = duration.getMillis();

        if (millis <= 0l)
            return 0l;

        return millis;
    }

    @Override
    public long getTotalTime() {
        if (endTime == null)
            return 0l;

        return new Duration(startTime, endTime).getMillis();
    }

    @Override
    public String getGivenAnswer(Question question) {
        return answerMap.get(question);
    }

    @Override
    public int getTotalPoints() {
        int total = questionSet.getInitialPoints();

        for (Question question : answerMap.keySet()) {
            String givenAnswer = answerMap.get(question);
            Set_Question sq = Set_Question.getSet_Question(questionSet, question);

            if (question.isCorrectAnswer(givenAnswer)) {
                total += sq.correctPoints;
            } else {
                total -= sq.incorrectPoints;
            }
        }

        return total;
    }
}