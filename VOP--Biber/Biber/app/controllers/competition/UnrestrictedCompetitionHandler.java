package controllers.competition;

import controllers.Application;
import models.Competition;
import models.Question;
import models.Set;
import play.mvc.Result;

public class UnrestrictedCompetitionHandler extends CompetitionHandler {

    private static final CompetitionHandler loggedInHandler = new UnrestrictedLoggedInCompetitionHandler();
    private static final CompetitionHandler anonymousHandler = new UnrestrictedAnonymousCompetitionHandler();

    private static CompetitionHandler getHandler(boolean isLoggedIn) {
        return isLoggedIn ? loggedInHandler : anonymousHandler;
    }

    @Override
    public Result beforeCompetition(Competition competition, Set questionSet) {
        return getHandler(Application.isLoggedIn()).beforeCompetition(competition, questionSet);
    }

    @Override
    public Result startCompetition(Competition competition, Set questionSet) {
        return getHandler(Application.isLoggedIn()).startCompetition(competition, questionSet);
    }

    @Override
    public Result showQuestion(Competition competition, Set questionSet, Question question, int questionIndex) {
        return getHandler(Application.isLoggedIn()).showQuestion(competition, questionSet, question, questionIndex);
    }

    @Override
    public Result answerQuestion(Competition competition, Set questionSet, Question question, int questionIndex, String givenAnswer) {
        return getHandler(Application.isLoggedIn()).answerQuestion(
                competition, questionSet, question,
                questionIndex, givenAnswer);
    }

    @Override
    public Result finishCompetition(Competition competition, Set questionSet) {
        return getHandler(Application.isLoggedIn()).finishCompetition(competition, questionSet);
    }
}
