package controllers.competition;

import controllers.Application;
import controllers.routes;
import models.*;
import org.joda.time.DateTime;
import play.mvc.Result;
import utils.LangMessages;
import views.html.competition.beforeCompetition;
import views.html.competition.showQuestion;

import static controllers.CompetitionController.ParseException;

public abstract class LoggedInCompetitionHandler extends CompetitionHandler {

    /**
     * Checks if the given Pupil has access to the given Competition, ie
     * answers "has the competition been opened for the given pupil?".
     * In case it was not opened, a ParseException is thrown, otherwise
     * this method does absolutely nothing.
     *
     * @param pupil
     * @param competition
     * @throws ParseException
     */
    protected void parseCompetitionOpened(Pupil pupil, Competition competition) throws ParseException {
        if (!pupil.findOpenCompetitions().contains(competition))
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.competition"))
            );
    }

    /**
     * Checks if the levels of the given pupil and questionSet match.
     * In case they don't a parseException is thrown.
     *
     * @param pupil
     * @param questionSet
     * @throws ParseException
     */
    protected void parseLevelMatches(Pupil pupil, Set questionSet) throws ParseException {
        if (pupil.getLevel() != null && !pupil.getLevel().equals(questionSet.level))
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.questionSet"))
            );
    }

    /**
     * Checks if we still have an unfinished competition running.
     * In case we do, a ParseException is thrown.
     *
     * @param pupil
     * @param competition
     * @param questionSet
     * @throws ParseException
     */
    protected void parseNoUnfinishedCompetitionRunning(Pupil pupil, Competition competition, Set questionSet) throws ParseException {
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        if (history != null) {
            // We have an unfinished competition
            // Is it the same (competition,questionset) we selected?
            if (history.competition.id.compareTo(competition.id)==0 && history.questionSet.id.compareTo(questionSet.id)==0) {
                // Yes, redirect to the first question of the competition
                throwParseException(redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1)));
            }

            // No, show error message
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("competition.take.stillHaveUnfinishedCompetition")
            );
        }
    }

    // Check if we have ever taken this specific (competition, question set) combination

    /**
     * Checks if the given pupil has already taken the given (competition, questionSet)-pair.
     * In case he does, a ParseException is thrown.
     *
     * @param pupil
     * @param competition
     * @param questionSet
     * @throws ParseException
     */
    protected void parseCompetitionNotAlreadyTaken(Pupil pupil, Competition competition, Set questionSet) throws ParseException {
        if (ParticipationHistory.getHistoryFor(pupil, competition, questionSet) != null)
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("competition.take.alreadyTaken")
            );
    }

    /**
     * Checks if the pupil has a running competition that mathces the given
     * (competition, questionSet)-pair.
     * In case he has no running competitions, or they don't match, a ParseException
     * is thrown.
     * Otherwise a ParticipationHistory is returned.
     *
     * @param pupil
     * @param competition
     * @param questionSet
     * @return
     * @throws ParseException
     */
    protected ParticipationHistory parseCompetitionMatchesRunningCompetition(Pupil pupil, Competition competition, Set questionSet) throws ParseException {
        ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
        if (history == null) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("common.notFound", LangMessages.get("common.competition"))
            );
        }

        if (history.competition.id.compareTo(competition.id) != 0 || history.questionSet.id.compareTo(questionSet.id) != 0) {
            throwParseException(
                    redirect(routes.ProfilesController.seeProfile()),
                    LangMessages.get("competition.take.stillHaveUnfinishedCompetition")
            );
        }

        return history;
    }

    /**
     * Checks if we have time left for the current Competition in the given ParticipationHistory.
     * In case we don't a ParseException is thrown.
     *
     * @param history
     * @throws ParseException
     */
    protected void parseTimeLeft(ParticipationHistory history) throws ParseException {
        if (history.getTimeLeft() == 0l)
            throw new ParseException(redirect(routes.CompetitionController.finishCompetition(history.competition.id, history.questionSet.level.name())));
    }

    @Override
    public Result beforeCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();

        try {
            parseCompetitionOpened(pupil, competition);
            parseLevelMatches(pupil, questionSet);
            parseNoUnfinishedCompetitionRunning(pupil, competition, questionSet);
            parseCompetitionNotAlreadyTaken(pupil, competition, questionSet);

            return ok(beforeCompetition.render(competition, questionSet));
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    @Override
    public Result startCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();
        try {
            parseCompetitionOpened(pupil, competition);
            parseLevelMatches(pupil, questionSet);
            parseNoUnfinishedCompetitionRunning(pupil, competition, questionSet);
            parseCompetitionNotAlreadyTaken(pupil, competition, questionSet);

            // Start the competition
            ParticipationHistory history = new ParticipationHistory(pupil, competition, questionSet, DateTime.now());
            history.save();

            // Go to the first question of the current question set
            return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1));
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    @Override
    public Result showQuestion(Competition competition, Set questionSet, Question question, int questionIndex) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();
        try {
            ParticipationHistory history = parseCompetitionMatchesRunningCompetition(pupil, competition, questionSet);
            parseTimeLeft(history);
            return ok(showQuestion.render(history, question, questionIndex));

        } catch (ParseException e) {
            return e.getResult();
        }
    }

    @Override
    public Result answerQuestion(Competition competition, Set questionSet, Question question, int questionIndex, String givenAnswer) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();
        try {
            ParticipationHistory history = parseCompetitionMatchesRunningCompetition(pupil, competition, questionSet);
            parseTimeLeft(history);

            // Have we already answered this question?
            AnswerHistory answer = AnswerHistory.getAnswerHistory(history, question);
            if (answer == null) {
                // No: add a new answer
                answer = new AnswerHistory(history, question, givenAnswer);
            } else {
                // Yes: update the answer
                answer.givenAnswer = givenAnswer;
            }

            answer.save();

            // Was this the last question?
            if (questionIndex == questionSet.size()) {
                // Yes: redirect back to the last question
                return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), questionIndex));
            }

            // No: Redirect to the next question
            return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), questionIndex+1));
        } catch (ParseException e) {
            return e.getResult();
        }
    }

    public abstract Result finishCompetition(Competition competition, Set questionSet);
}
