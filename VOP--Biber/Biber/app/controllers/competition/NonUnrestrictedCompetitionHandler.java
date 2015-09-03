package controllers.competition;

import controllers.Application;
import controllers.CompetitionController;
import controllers.routes;
import models.Competition;
import models.ParticipationHistory;
import models.Pupil;
import models.Set;
import play.mvc.Result;
import utils.LangMessages;
import views.html.competition.afterCompetition;

public class NonUnrestrictedCompetitionHandler extends LoggedInCompetitionHandler {
    @Override
    public Result finishCompetition(Competition competition, Set questionSet) {
        Pupil pupil = Application.getCurrentlyLoggedInPupil();

        try {
            // Finish the competition
            ParticipationHistory history = parseCompetitionMatchesRunningCompetition(pupil, competition, questionSet);
            history.finish();

            flash("success", LangMessages.get("competition.take.competitionFinished"));
            return redirect(routes.ProfilesController.seeProfile());
        } catch (CompetitionController.ParseException e) {
            return e.getResult();
        }
    }
}
