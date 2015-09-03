package models;

import com.avaje.ebean.Ebean;
import org.joda.time.DateTime;
import org.joda.time.Duration;
import org.joda.time.Instant;
import org.joda.time.Period;
import play.db.ebean.Model;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.ManyToMany;
import javax.persistence.ManyToOne;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@Entity
public class ParticipationHistory extends Model implements History {
    @Id
    public Long id;

    @ManyToOne
    public Pupil participant;

    @ManyToOne
    public Competition competition;

    @ManyToOne
    public Set questionSet;

    public DateTime startTime;
    public DateTime endTime;
    public long extraTime;              // Extra time (in ms)

    public static Finder<Long, ParticipationHistory> find = new Finder(Long.class, ParticipationHistory.class);

    public ParticipationHistory(Pupil participant, Competition competition, Set questionSet, DateTime startTime) {
        this(participant, competition, questionSet, startTime, null);
    }

    public ParticipationHistory(Pupil participant, Competition competition, Set questionSet,
                                DateTime startTime, DateTime endTime) {
        this.participant = participant;
        this.competition = competition;
        this.questionSet = questionSet;
        this.startTime = startTime;
        this.endTime = endTime;
        this.extraTime = 0;
    }

    @Override
    public Competition getCompetition() {
        return competition;
    }

    @Override
    public Set getQuestionSet() {
        return questionSet;
    }
    public long getTimeLeft() {
        Duration duration = new Duration(
                new Instant(),
                startTime.plus(questionSet.timeLimit * 1000).plus(extraTime)
        );

        long millis = duration.getMillis();

        if (millis <= 0l)
            return 0l;

        return millis;
    }

    @Override
    public String getGivenAnswer(Question question) {
        AnswerHistory h = AnswerHistory.getAnswerHistory(this, question);
        return (h == null) ? null : h.givenAnswer;
    }

    /**
     *
     * @return  Returns the number of milliseconds it took for the user
     *          to finish the competition associated with this PariticpationHistory.
     */
    public long getTotalTime() {
        if (endTime == null)
            return 0l;

        Duration duration = new Duration(startTime, endTime);
        return duration.getMillis();
    }

    /**
     * @return  Checks if the pupil associated with this history has
     *          finished the competition linked with this history and
     *          returns true if that's the case, false otherwise.
     */
    public boolean isFinished() {
        return endTime != null;
    }

    public void giveExtraTime(Period extraTime) {
        this.extraTime += (extraTime.getHours()*3600+extraTime.getMinutes()*60+extraTime.getSeconds()) * 1000;
    }

    /**
     * Reopens the competition with the given timeLimit in seconds.
     * This also resets the endTime
     *
     * @param newTimeLimit  New timeLimit for the reopened competition
     * @param deleteAnswers Indicates wether or not we should delete
     *                      any given answers
     */
    public void reopenCompetition(Period newTimeLimit, boolean deleteAnswers) {
        endTime = null;
        extraTime = DateTime.now()
                .plus(newTimeLimit)
                .minus(startTime.getMillis())
                .minus(questionSet.timeLimit * 1000)
                .getMillis();

        if (deleteAnswers)
            Ebean.delete(AnswerHistory.getAnswerHistories(this).values());
    }

    /**
     * Resets the startTime of the history and deletes the endTime and extraTime
     *
     * @param newStartTime   The new start time for the history
     * @param deleteAnswers  Indicates wether or not we should delete the given answers
     */
    public void resetHistory(DateTime newStartTime, boolean deleteAnswers) {
        endTime = null;
        extraTime = 0;
        startTime = newStartTime;

        if (deleteAnswers)
            Ebean.delete(AnswerHistory.getAnswerHistories(this).values());
    }

    /**
     * In case this history corresponds to a competition that was not finished,
     * using this method will finish the competition by filling in the endTime
     * to the current time.
     * Note: A boundary is put on the maximum time a competition has ended.
     * In case we did not finish the competition within the timelimit,
     * endTime will be set to startTime + timeLimit
     */
    public void finish() {
        if (endTime != null)
            return;

        DateTime now = DateTime.now();
        DateTime maxEndTime = startTime.plus(questionSet.timeLimit * 1000).plus(extraTime);

        if (now.isAfter(maxEndTime))
            endTime = maxEndTime;
        else
            endTime = now;

        this.save();
    }

    /**
     * Get the total points obtained for the competition and pupil corresponding with this class
     */
    public int getTotalPoints() {
        int totalPoints = questionSet.getInitialPoints();
        boolean isCorrect = true;
        Map<Question, AnswerHistory> map = AnswerHistory.getAnswerHistories(this);
        for (Map.Entry<Question, AnswerHistory> entry : map.entrySet()) {
            Question currentQuestion = entry.getKey();
            isCorrect = currentQuestion.isCorrectAnswer(entry.getValue().givenAnswer);
            Set_Question sq = Set_Question.getSet_Question(questionSet, currentQuestion);
            if (isCorrect) {
                totalPoints = totalPoints + sq.correctPoints;
            } else {
                totalPoints = totalPoints - sq.incorrectPoints;
            }
        }
        return totalPoints;
    }

    /**
     * @param pupil
     *
     * @return  Returns a list of ParticipationHistories for the given Pupil
     */
    public static List<ParticipationHistory> getHistoryFor(Pupil pupil) {
        return find.where()
                    .eq("participant", pupil).findList();
    }

    /**
     * Returns the ParticipantHistory given the Pupil, Competition and Set
     *
     * @param pupil
     * @param competition
     * @param questionSet
     *
     * @return  Returns the ParticipantHistory for the given combination of
     *          (Pupil, Competition, Set), or null in case there is no
     *          matching ParticipationHistory for the given combination.
     */
    public static ParticipationHistory getHistoryFor(Pupil pupil, Competition competition, Set questionSet) {
        return find.where()
                .eq("participant", pupil)
                .eq("competition", competition)
                .eq("questionSet", questionSet).findUnique();
    }

    public static List<ParticipationHistory> getHistoryFor(Set questionSet){
        return find.where().eq("questionSet",questionSet).findList();
    }

    /**
     * Returns the ParticipantHistoryS for a list of pupils, given a Competition and Set
     *
     * @param pupils
     * @param competition
     * @param questionSet
     *
     * @return  Returns a List ParticipantHistoryS for the given combination of
     *          (Pupil, Competition, Set), for all pupils.
     */
    public static List<ParticipationHistory> getHistoryFor(List<Pupil> pupils, Competition competition, Set questionSet) {
        List<ParticipationHistory> histories = new ArrayList<ParticipationHistory>(pupils.size());

        for (Pupil pupil : pupils) {
            histories.add(getHistoryFor(pupil, competition, questionSet));
        }

        return histories;
    }

    /**
     * Returns the ParticipationHistory associated with a given pupil and competition
     *
     * @param pupil
     * @param competition
     */
    public static ParticipationHistory getHistoryFor(Pupil pupil, Competition competition) {
        return find.where()
                .eq("participant", pupil)
                .eq("competition", competition)
            .findUnique();
    }

    public static List<ParticipationHistory> getHistoryFor(Competition c){
        return find.where().eq("competition",c).findList();
    }

    /**
     * Returns a ParticipationHistory for every pupil in the given pupils List
     *
     * @param pupils
     * @param competition
     */
    public static List<ParticipationHistory> getHistoryFor(List<Pupil> pupils, Competition competition) {
        List<ParticipationHistory> histories = new ArrayList<ParticipationHistory>();

        for (Pupil pupil : pupils) {
            histories.add(getHistoryFor(pupil, competition));
        }

        return histories;
    }

    public static ParticipationHistory findById(long id){
        return ParticipationHistory.find.where().eq("id",id).findUnique();
    }

    /**
     * Returns a ParticipationHistory for the given Pupil, which is unfinished (if any).
     * In this context, an unfinished history is a ParticipationHistory
     * so that the competition associated
     * with the history was never finished by the given Pupil.
     *
     * @param pupil     The pupil for which we want an unfinished history
     *
     * @return
     */
    public static ParticipationHistory getHistoryWithUnfinishedCompetitionFor(Pupil pupil) {
        // Find out if there is a history which does not have an endTime (there should only
        // be one !)
        return find.where()
                .eq("participant", pupil)
                .isNull("endTime")
                .findUnique();
    }


    public static List<ParticipationHistory> getCompetitionStats(CompetitionType type) {
        return ParticipationHistory.find.where().eq("competition.compType", type).findList();
    }
    /**
     * Returns a List of ParticipationHistoryS for the given List of PupilS,
     * which is unfinished (if any).
     * In this context, an unfinished history is a ParticipationHistory
     * so that the competition associated
     * with the history was never finished by the given Pupil.
     *
     * @param pupils     The pupils for which we want an unfinished history
     *
     * @return
     */
    public static List<ParticipationHistory> getHistoryWithUnfinishedCompetitionFor(List<Pupil> pupils) {
        List<ParticipationHistory> histories = new ArrayList<ParticipationHistory>(pupils.size());

        for (Pupil pupil : pupils) {
            ParticipationHistory history = getHistoryWithUnfinishedCompetitionFor(pupil);
            if (history != null)
                histories.add(history);
        }

        return histories;
    }
    
    /**
     * Get all history for a list of pupils. To be used for the merging of pupils
     * @param pupils
     * @return
     */
    public static List<ParticipationHistory> getAllHistory(List<Pupil> pupils){
        List<ParticipationHistory> histories = new ArrayList<ParticipationHistory>();
        for (Pupil pupil : pupils) {
            histories.addAll(find.where().eq("participant", pupil).findList());
        }
        return histories;
    }
}
