package controllers;

import controllers.competition.CompetitionHandler;
import controllers.competition.NonUnrestrictedCompetitionHandler;
import controllers.competition.UnrestrictedCompetitionHandler;
import models.*;
import play.data.Form;
import play.data.validation.Constraints;
import play.mvc.Controller;
import play.mvc.Result;
import utils.LangMessages;
import java.util.Map;
import java.util.TreeMap;

/**
 * This class acts as a controller for all actions during the participation in a
 * Competition.
 * Note that when we say participate "in a Competition", we actually mean that we
 * are participing in a (Competition, questionSet)-pair, since for one Competition
 * there are different questionSets for each level.
 * The same holds through when we mention opening and closing a Competition.
 */
public class CompetitionController extends Controller {

    private static Map<CompetitionType, CompetitionHandler> handlerMap;
    static {
        handlerMap = new TreeMap<CompetitionType, CompetitionHandler>();

        handlerMap.put(CompetitionType.UNRESTRICTED, new UnrestrictedCompetitionHandler());
        handlerMap.put(CompetitionType.LOCAL, new NonUnrestrictedCompetitionHandler());
        handlerMap.put(CompetitionType.OFFICIAL, new NonUnrestrictedCompetitionHandler());
    }

    public static void throwParseException(Result result) throws ParseException {
        throw new ParseException(result);
    }

    public static void throwParseException(Result result, String message) throws ParseException {
        flash("important", message);
        throwParseException(result);
    }

    /**
     * Checks if the competition for the given competitionId exists.
     * In case it does not, it throws a parseException
     *
     * @param competitionId the id of the competition
     * @return              Returns the Competition for the given competitionId
     * @throws ParseException   Throws a ParseException in case there is no Competition
     *                          for the given id.
     */
    private static Competition parseCompetition(long competitionId) throws ParseException {
        Competition competition = Competition.findById(competitionId);
        if (competition == null || competition.isOpen != Competition.VISIBLE) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.competition"))
            );
        }

        return competition;
    }

    /**
     * Checks if the Level for the given String exists. In case it
     * does the Level is returned, otherwise a ParseException is thrown.
     *
     * @param level String for which we want to check if there exists a level
     *              with this name.
     *
     * @return      Returns the Level with name for the given string in case it
     *              exists.
     *
     * @throws ParseException Throws a ParseException in case no level is found
     *                        with the given name.
     */
    private static Level parseLevel(String level) throws ParseException {
        Level l = null;
        try {
            l = Level.valueOf(level);
        } catch (Exception e) {
        }

        if (l == null) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.questionSet"))
            );
        }

        return l;
    }

    /**
     * Checks if there exists a questionSet for the given Competition and Level.
     * In case it does, the Set is returned, otherwise a ParseException is thrown.
     *
     * @param competition   Competition for which we want to match the questionSet
     *
     * @param level         The Level for which we want to match the questionSet within
     *                      the given Competition.
     *
     * @return              Returns the questionSet in case it exists.
     *
     * @throws ParseException   Throws a ParseException in case there is no questionSet which
     *                          matches the given arguments.
     */
    private static Set parseQuestionSet(Competition competition, Level level) throws ParseException {
        Set s = competition.questionSets.get(level);
        if (s == null) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.questionSet"))
            );
        }

        return s;
    }

    /**
     * Checks if a Question exists within the given questionSet and with index questionIndex.
     * In case it does, it is returned, otherwise a ParseException is thrown.
     *
     * @param questionSet       questionSet which possibly contains the Question
     * @param questionIndex     the index of the Question within the Set
     * @return                  Returns the Question in case it exists
     * @throws ParseException   Throws a ParseException in case the Question does not exist.
     */
    private static Question parseQuestion(Set questionSet, int questionIndex) throws ParseException {
        if (questionIndex <= 0 || questionIndex > questionSet.size()) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.question"))
            );
        }

        Question question = questionSet.getSetQuestions().get(questionIndex-1).question;
        if (question == null) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.question"))
            );
        }

        return question;
    }

    /**
     * Returns a CompetitionHandler for the given Competition.
     * This CompetitionHandler will handle all specific case for the
     * given Competition when participating in this Competition.
     * In case the CompetitionHandler does not exist, a ParseException is thrown.
     *
     * @param competition       Competition for which we the CompetitionHandler
     * @return                  Returns the CompetitionHandler in case it exists.
     * @throws ParseException   Throws a ParseException in case no CompetitionHandler is found.
     */
    public static CompetitionHandler getHandler(Competition competition) throws ParseException {
        CompetitionHandler handler = handlerMap.get(competition.compType);
        if (handler == null)
            throwParseException(redirect(routes.ProfilesController.seeProfile()));

        return handler;
    }

    /**
     * This method handles all functionality that should happen before a competition starts:
     * general information about the competition should be shown, as well a button to start
     * the competition.
     *
     * @param competitionId The id of the competition.
     * @param level         The name of the level of the questionSet within the competition
     *                      we are participating in.
     * @return
     */
    public static Result beforeCompetition(long competitionId, String level) {
        try {
            Competition c = parseCompetition(competitionId);
            Level l = parseLevel(level);
            Set s = parseQuestionSet(c, l);
            CompetitionHandler h = getHandler(c);

            return h.beforeCompetition(c, s);
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    /**
     * This method is called when a Competition starts, all it does it start the competition
     * for the given competitionId, and the questionSet within the competition whose Level
     * has name level.
     *
     * @param competitionId id of the Competition.
     * @param level         name of the Level of the questionSet
     * @return
     */
    public static Result startCompetition(long competitionId, String level) {
        try {
            Competition c = parseCompetition(competitionId);
            Level l = parseLevel(level);
            Set s = parseQuestionSet(c, l);
            CompetitionHandler h = getHandler(c);
            return h.startCompetition(c, s);
        } catch (ParseException e) {
            return e.getResult();
            
        }
    }

    /**
     * This method shows a question for the given parameters.
     *
     * @param competitionId id of the Competition
     * @param level         name of the Level of the questionSet within the competition
     * @param questionIndex index of the question within the questionSet
     * @return
     */
    public static Result showQuestion(long competitionId, String level, int questionIndex) {
        try {
            Competition c = parseCompetition(competitionId);
            Level l = parseLevel(level);
            Set s = parseQuestionSet(c, l);
            Question q = parseQuestion(s, questionIndex);
            CompetitionHandler h = getHandler(c);

            return h.showQuestion(c, s, q, questionIndex);
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    /**
     * This method handles answering a question, when called it assumes a form
     * with a field named "answer" is submitted.
     *
     * @param competitionId     id of the Competition for which we want to answer a Question
     * @param level             name of the Level of the questionSet within the Competition
     * @param questionIndex     index of the question within the questionSet
     * @return
     */
    public static Result answerQuestion(long competitionId, String level, int questionIndex) {
        try {
            Competition c = parseCompetition(competitionId);
            Level l = parseLevel(level);
            Set s = parseQuestionSet(c, l);
            Question q = parseQuestion(s, questionIndex);
            CompetitionHandler h = getHandler(c);

            // Check the given answer
            Form<Answer> answerForm = new Form<Answer>(Answer.class).bindFromRequest();
            if (answerForm.hasErrors())
                return badRequest("");

            String givenAnswer = answerForm.get().answer;
            if (givenAnswer == null || "".equals(givenAnswer))
                return badRequest("");

            return h.answerQuestion(c, s, q, questionIndex, givenAnswer);
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    /**
     * This method finishes a Competition.
     *
     * @param competitionId the id of the Competition we want to finish
     * @param level         the name of the Level of the questionSet within the Competition.
     * @return
     */
    public static Result finishCompetition(long competitionId, String level) {
        try {
            Competition c = parseCompetition(competitionId);
            Level l = parseLevel(level);
            Set s = parseQuestionSet(c, l);
            CompetitionHandler h = getHandler(c);
            //TODO: implement show stats

            return h.finishCompetition(c, s);
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    public static class ParseException extends Exception {
        private final Result result;
        public ParseException(Result result) {
            this.result = result;
        }

        public Result getResult() {
            return result;
        }
    }

    public static class Answer {
        @Constraints.Required
        public String answer;
    }
}
