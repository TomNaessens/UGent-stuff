package controllers.competition;

import controllers.Application;
import controllers.CompetitionController;
import controllers.routes;
import models.*;
import org.joda.time.DateTime;
import play.mvc.Result;
import views.html.competition.afterCompetition;
import views.html.competition.beforeCompetition;

public class UnrestrictedLoggedInCompetitionHandler extends LoggedInCompetitionHandler {
    @Override
    public Result beforeCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();

        try {
            parseNoUnfinishedCompetitionRunning(pupil, competition, questionSet);
            parseCompetitionNotAlreadyTaken(pupil, competition, questionSet);

            return ok(beforeCompetition.render(competition, questionSet));
        } catch (CompetitionController.ParseException e) {
            return e.getResult();
        }
    }

    @Override
    public Result startCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();

        try {
            parseNoUnfinishedCompetitionRunning(pupil, competition, questionSet);
            parseCompetitionNotAlreadyTaken(pupil, competition, questionSet);

            // Start the competition
            ParticipationHistory history = new ParticipationHistory(pupil, competition, questionSet, DateTime.now());
            history.save();

            // Go to the first question of the current question set
            return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1));
        } catch (CompetitionController.ParseException e) {
            return e.getResult();
        }
    }

    @Override
    public Result finishCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();

        try {
            // Finish the competition
            ParticipationHistory history = parseCompetitionMatchesRunningCompetition(pupil, competition, questionSet);
            history.finish();

            return ok(afterCompetition.render(history, new CompetitionComparison(history)));

        } catch (CompetitionController.ParseException e) {
            return e.getResult();
        }
    }
}
