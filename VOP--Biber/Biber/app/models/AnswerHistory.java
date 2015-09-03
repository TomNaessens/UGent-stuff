package models;

import play.db.ebean.Model;

import javax.persistence.*;
import java.util.List;
import java.util.Map;

@Entity
public class AnswerHistory extends Model {
    // TODO: do we need an ID here?
    @Id @GeneratedValue
    public Long id;

    @ManyToOne(cascade = CascadeType.ALL)
    public ParticipationHistory history;
    @ManyToOne(cascade = CascadeType.DETACH)
    public Question question;

    public String givenAnswer;

    public AnswerHistory(ParticipationHistory history, Question question, String givenAnswer) {
        this.history = history;
        this.question = question;
        this.givenAnswer = givenAnswer;
    }

    public static Finder<Long, AnswerHistory> find = new Finder(Long.class, AnswerHistory.class);

    /**
     * Returns a map of questions to given answers for a given ParticipationHistory
     *
     * @param history   ParticipationHistory for which we want the answers
     *                  to the questions
     *
     * @return          Returns a Map of QuestionS to AnswerHistoryS which contains the
     *                  answers given to all the questions related to the given
     *                  ParticipationHistory
     */
    public static Map<Question, AnswerHistory> getAnswerHistories(ParticipationHistory history) {
        return (Map<Question, AnswerHistory>)
                find.where()
                    .eq("history", history)
                .setMapKey("question").findMap();
    }

    /**
     * @param history   ParticipationHistory for which we want to count the number of AnswerHistoryS
     *
     * @return  Returns the number AnswerHistoryS that correspond with the given ParticipationHistory
     */
    public static int countAnswerHistories(ParticipationHistory history) {
        return find.where().eq("history", history).findRowCount();
    }

    /**
     * Returns an AnswerHistory for a given ParticipationHistory and question
     *
     * @param history   ParticipationHistory for which we want the answer
     *
     * @param question  Question for which we want the answer
     *
     * @return          Returns a AnswerHistory which contains the
     *                  answers given to the specifed Question related
     *                  to the given ParticipationHistory
     */
    public static AnswerHistory getAnswerHistory(ParticipationHistory history, Question question) {
        return find.where()
                    .eq("history", history)
                    .eq("question", question)
                .findUnique();
    }
}
