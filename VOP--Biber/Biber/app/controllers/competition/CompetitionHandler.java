package controllers.competition;

import controllers.CompetitionController;
import models.Competition;
import models.Question;
import models.Set;
import play.mvc.Controller;
import play.mvc.Result;

public abstract class CompetitionHandler extends Controller {

    protected void throwParseException(Result result) throws CompetitionController.ParseException {
        CompetitionController.throwParseException(result);
    }

    protected void throwParseException(Result result, String message) throws CompetitionController.ParseException {
        CompetitionController.throwParseException(result, message);
    }

    public abstract Result beforeCompetition(Competition competition, Set questionSet);

    public abstract Result startCompetition(Competition competition, Set questionSet);

    public abstract Result showQuestion(Competition competition, Set questionSet, Question question, int questionIndex);

    public abstract Result answerQuestion(Competition competition, Set questionSet, Question question,
                                          int questionIndex, String givenAnswer);

    public abstract Result finishCompetition(Competition competition, Set questionSet);

}
