package controllers.competition;

import controllers.routes;
import models.*;
import play.mvc.Result;
import utils.LangMessages;
import views.html.competition.beforeCompetition;

public class UnrestrictedAnonymousCompetitionHandler extends CompetitionHandler {

    private static AnonymousCompetitionManager manager = AnonymousCompetitionManager.getSingleton();

    @Override
    public Result beforeCompetition(Competition competition, Set questionSet) {
        // Do we have a competition running?
        if (manager.hasCompetitionRunning()) {
            // Is it this competition?
            if (manager.getHistoryForRunningCompetition().competition.id.compareTo(competition.id) == 0)
                return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1));

            flash(LangMessages.get("competition.take.stillHaveUnfinishedCompetition"));
            return redirect(routes.Competitions.renderUnrestrictedCompetitions());
        }

        return ok(beforeCompetition.render(competition, questionSet));
    }

    @Override
    public Result startCompetition(Competition competition, Set questionSet) {
        // Do we have a competition running?
        if (manager.hasCompetitionRunning()) {
            // Is it this competition?
            if (manager.getHistoryForRunningCompetition().competition.id == competition.id)
                return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1));

            flash(LangMessages.get("competition.take.stillHaveUnfinishedCompetition"));
            return redirect(routes.Competitions.renderUnrestrictedCompetitions());
        }

        // Start the competition
        manager.startCompetition(competition, questionSet);

        return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), 1));
    }

    @Override
    public Result showQuestion(Competition competition, Set questionSet, Question question, int questionIndex) {
        if (!manager.hasCompetitionRunning())
            return redirect(routes.Competitions.renderUnrestrictedCompetitions());

        AnonymousHistory history = manager.getHistoryForRunningCompetition();

        return ok(views.html.competition.showQuestion.render(history, question, questionIndex));
    }

    @Override
    public Result answerQuestion(Competition competition, Set questionSet, Question question, int questionIndex, String givenAnswer) {
        if (!manager.hasCompetitionRunning())
            return redirect(routes.Competitions.renderUnrestrictedCompetitions());

        manager.answerQuestion(question, givenAnswer);

        int nextIndex = questionIndex + 1;
        if (nextIndex > questionSet.size())
            nextIndex -= 1;

        return redirect(routes.CompetitionController.showQuestion(competition.id, questionSet.level.name(), nextIndex));
    }

    @Override
    public Result finishCompetition(Competition competition, Set questionSet) {
        if (!manager.hasCompetitionRunning())
            return redirect(routes.Competitions.renderUnrestrictedCompetitions());

        AnonymousHistory history = manager.getHistoryForRunningCompetition();

        manager.finishCompetition();

        return ok(views.html.competition.afterCompetition.render(history,null));
    }
}
