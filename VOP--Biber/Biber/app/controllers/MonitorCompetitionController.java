package controllers;

import com.avaje.ebean.Ebean;
import com.avaje.ebean.SqlUpdate;
import models.*;
import models.Class;
import org.codehaus.jackson.node.JsonNodeFactory;
import org.codehaus.jackson.node.ObjectNode;
import org.joda.time.DateTime;
import org.joda.time.Duration;
import org.joda.time.Period;
import org.joda.time.format.DateTimeFormat;
import org.joda.time.format.DateTimeFormatter;
import org.joda.time.format.PeriodFormatter;
import org.joda.time.format.PeriodFormatterBuilder;
import play.data.Form;
import play.data.validation.Constraints;
import play.libs.F;
import play.libs.Json;
import play.libs.Time;
import play.mvc.Controller;
import play.mvc.Result;
import utils.LangMessages;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MonitorCompetitionController extends Controller {

    private static final PeriodFormatter timeFormatter = new PeriodFormatterBuilder()
            .appendHours().appendLiteral(":")
            .appendMinutes().appendLiteral(":")
            .appendSeconds()
            .toFormatter();

    public static Result grantGraceTime(Long competitionId) {
        Form<Time> form = new Form<Time>(Time.class).bindFromRequest();
        if (!form.hasErrors()) {
            // Get the competition and pupil
            Competition competition = Competition.findById(competitionId);
            Pupil pupil = Pupil.findPupilByBebrasID(form.get().pupil);

            if (competition != null && pupil != null) {
                try {
                    Period graceTime = timeFormatter.parsePeriod(form.get().time);

                    // Set graceTime
                    ParticipationHistory history = ParticipationHistory.getHistoryWithUnfinishedCompetitionFor(pupil);
                    if (history.competition.id.compareTo(competitionId) == 0) {
                        history.giveExtraTime(graceTime);
                        history.save();
                    }
                } catch (Exception e) {
                    // Do nothing, user just gave in wrong information...
                }
            }

        }

        return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
    }

    public static Result deleteHistory(Long competitionId) {
        Form<DeleteHistory> form = new Form<DeleteHistory>(DeleteHistory.class).bindFromRequest();

        if (!form.hasErrors()) {
            // Get the competition and pupil
            Competition competition = Competition.findById(competitionId);
            Pupil pupil = Pupil.findPupilByBebrasID(form.get().pupil);

            if (competition != null && pupil != null) {
                ParticipationHistory history = ParticipationHistory.getHistoryFor(pupil, competition);

                if (history != null) {
                    // TODO: clean up ugly way to avoid foreign key constraint error once ebean fix their stuff
                    String[] queries = {
                            "DELETE FROM answer_history WHERE history_id=" + history.id,
                            "DELETE FROM participation_history WHERE id=" + history.id
                    };

                    for (String q : queries) {
                        SqlUpdate u = Ebean.createSqlUpdate(q);
                        Ebean.execute(u);
                    }
                }
            }
        }

        return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
    }

    public static Result reopenCompetition(Long competitionId) {
        Form<Time> form = new Form<Time>(Time.class).bindFromRequest();

        if (!form.hasErrors()) {

            // Get the competition and pupil
            Competition competition = Competition.findById(competitionId);
            Pupil pupil = Pupil.findPupilByBebrasID(form.get().pupil);

            if (competition != null && pupil != null) {

                try {
                    Period competitionTime = timeFormatter.parsePeriod(form.get().time);

                    // Get the history
                    ParticipationHistory history = ParticipationHistory.getHistoryFor(pupil, competition);

                    if (history != null) {
                        // Reopen the competition
                        history.reopenCompetition(competitionTime, false);
                        history.save();
                    }

                } catch (Exception e) {
                    // Do nothing, user just gave in wrong information...
                }
            }

        }

        return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
    }

    public static Result monitorCompetition(Long competitionId) {
        // Get the competition
        Competition competition = Competition.findById(competitionId);
        if (competition == null)
            return badRequest(LangMessages.get("common.notFound"), LangMessages.get("common.competition"));

        return ok(views.html.teacher.monitorCompetition.render(competition));
    }

    /**
     * Returns the status of the pupils which are allowed to participate in
     * the competition with given competionId in a JSON format:
     *
     * {
     *  classId1 : {
     *      name : "class1",
     *      pupils : {
     *          "bebrasId1" : {
     *              firstName : "fn1",
     *              lastName  : "ln1",
     *              status    : "ONLINE"
     *          },
     *          "bebrasId2" : {
     *              firstName     : "fn2",
     *              lastName      : "ln2",
     *              status        : "FINISHED",
     *              time          : 10000   // Time in ms
     *          },
     *          //...
     *      }
     *  },
     *  //...
     * }
     * @param competitionId
     * @return
     */
    public static Result getPupilsStatusForCompetition(Long competitionId) {
        ObjectNode result = Json.newObject();

        // Get the competition
        Competition competition = Competition.findById(competitionId);
        if (competition == null)
            return badRequest();

        // 1. Get all classes participating in this competition
        List<Class> classes = competition.getParticipatingClasses(session("bebrasId"));

        for (Class clazz : classes) {
            // classId : { "name" : "class1", "pupils" : {...} }
            ObjectNode classNode = JsonNodeFactory.instance.objectNode();
            classNode.put("name", clazz.name);

            ObjectNode pupilsNode = JsonNodeFactory.instance.objectNode();
            classNode.put("pupils", pupilsNode);

            // 2. Get all pupils in each class
            List<Pupil> pupils = Pupil.findPupilsFromClass(clazz);

            // 3. Get all participation histories for these pupils
            List<ParticipationHistory> histories = ParticipationHistory.getHistoryFor(pupils, competition);

            for (int i=0; i < pupils.size(); ++i) {
                Pupil pupil = pupils.get(i);
                ParticipationHistory history = histories.get(i);

                // pupilId : { firstName : _, lastName : _, status : _, timeremaing : _ }
                ObjectNode pupilNode = JsonNodeFactory.instance.objectNode();
                pupilNode.put("firstName", pupil.firstName);
                pupilNode.put("lastName", pupil.lastName);
                pupilNode.put("online", pupil.isOnline());

                models.Status s = pupil.getStatus(history);
                pupilNode.put("status", LangMessages.get(s.toString()));

                if (s == models.Status.STARTED) {
                    pupilNode.put("time", history.getTimeLeft());   // Time left
                    pupilNode.put("answered", AnswerHistory.countAnswerHistories(history)); // Number of questions answered
                    pupilNode.put("numberOfQuestions", history.questionSet.getSetQuestions().size());     // Total number of questions
                }

                pupilsNode.put(pupil.bebrasId, pupilNode);
            }

            result.put(Long.toString(clazz.id), classNode);
        }

        return ok(result);
    }

    public static class Time {
        @Constraints.Required
        public String time;
        @Constraints.Required
        public String pupil;

        public String validate() {
            if (!time.matches("^[0-9]?[0-9](:[0-9]?[0-9]){2}$"))
                return "Invalid time format";

            return null;
        }
    }

    public static class DeleteHistory {
        @Constraints.Required
        public String pupil;
    }
}
