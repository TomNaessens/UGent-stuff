package models;

import org.joda.time.DateTime;
import play.mvc.Controller;

import java.util.HashMap;
import java.util.Map;
import java.util.UUID;

public class AnonymousCompetitionManager extends Controller {
    private Map<String, AnonymousHistory> historyMap;

    private static AnonymousCompetitionManager singleton = null;

    public static AnonymousCompetitionManager getSingleton() {
        if (singleton == null)
            singleton = new AnonymousCompetitionManager();

        return singleton;
    }

    private AnonymousCompetitionManager() {
        historyMap = new HashMap<String, AnonymousHistory>();
    }

    /**
     * @return Returns the UUID for the current anonymous user, in
     *         case he doesn't have one, a new one is generated.
     */
    private String getUUID() {
        String uuid = session().get("UUID");
        if (uuid == null) {
            uuid = UUID.randomUUID().toString();
            session("UUID", uuid);
        }

        return uuid;
    }

    /**
     * Checks if the current anonymous user has a running competition
     */
    public boolean hasCompetitionRunning() {
        return historyMap.get(getUUID()) != null;
    }

    /**
     * @return  Returns the history for the current running competition
     */
    public AnonymousHistory getHistoryForRunningCompetition() {
        return historyMap.get(getUUID());
    }

    /**
     * Starts a new competition for the current anonymous user
     *
     * @param competition   Competition we want to start
     * @param questionSet   QuestionSet we want to start
     */
    public void startCompetition(Competition competition, Set questionSet) {
        AnonymousHistory history = new AnonymousHistory(competition, questionSet);

        historyMap.put(getUUID(), history);
    }

    /**
     * Gives an answer to a question in the current competition
     *
     * @param question      the Question we give an answer to
     * @param givenAnswer   answer given by the anonymous user
     */
    public void answerQuestion(Question question, String givenAnswer) {
        AnonymousHistory history = historyMap.get(getUUID());

        history.answerMap.put(question, givenAnswer);
    }

    /**
     * Finishes the current running competition
     */
    public void finishCompetition() {
        AnonymousHistory history = historyMap.get(getUUID());
        history.endTime = DateTime.now();

        // Loop over all questions we answered in the history,
        // and fill in the anonymous user stats for that question
        for (Question q : history.answerMap.keySet()) {
            Anonymous_User_Stats stats = Anonymous_User_Stats.findAnonymousStats(q, history.questionSet);

            if (stats == null) {
                stats = new Anonymous_User_Stats(q, history.questionSet);
            }

            if (q.isCorrectAnswer(history.answerMap.get(q)))
                stats.incrementCorrect();
            else
                stats.incrementWrong();

            stats.save();
        }

        // Remove this history from the histories
        historyMap.remove(getUUID());
    }


}
