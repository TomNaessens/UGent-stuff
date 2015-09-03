package controllers;

import controllers.security.SecuredOrganizer;
import controllers.security.SecuredPupil;
import controllers.security.SecuredTeacher;
import models.*;
import models.Class;
import models.Set;
import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import play.data.Form;
import play.data.validation.Constraints;
import play.mvc.Controller;
import play.mvc.Result;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.*;

import play.mvc.Security;
import utils.LangMessages;
import views.html.organizer.viewQuestionSetStats;
import views.html.teacher.downloadStatistics;
import views.html.teacher.viewAllStatsForClass;
import views.html.pupil.viewStatsCompetition;
import views.html.organizer.questionStats;
import views.html.teacher.competitionStats;
import views.html.organizer.top20;

public class Statistics extends Controller {

    @Security.Authenticated(SecuredOrganizer.class)
    public static Result viewQuestionSetStatistics(Long setId){
        Set s = Set.findById(setId);
        List<ParticipationHistory> pList = ParticipationHistory.getHistoryFor(s);
        if(pList.size() == 0)  {
            flash("important",LangMessages.get("nostats"));
        }
        int range = s.getInitialPoints()+s.getAllCorrectPoints()+1;
        int participants = 0;
        int[] points = new int[range];
        for(ParticipationHistory p : pList){
            points[p.getTotalPoints()]++;
        }
        List<Integer> l = new ArrayList<Integer>();

        for(int p : points){
            l.add(p);
            participants+=p;
        }
        List<Question> qList;
        if(pList.size() > 0){
            qList = Set.getQuestions(s);
        }
        else {
            qList = new ArrayList<>();
        }
        return ok(viewQuestionSetStats.render(setId,l, participants,qList));
    }

    public static Result showStats(Long competitionId){
        Form<showStats> form = new Form<showStats>(showStats.class).bindFromRequest();
        String bebrasId = form.get().pupil;
        if (!form.hasErrors()) {
            //Collect data

            Competition competition = Competition.findById(competitionId);
            if(competition.isOpen != 2 && competition.compType == CompetitionType.OFFICIAL){
                flash("important",LangMessages.get("closeFirst"));
                return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
            }
            Pupil pupil = Pupil.findPupilByBebrasID(bebrasId);

            ParticipationHistory p = ParticipationHistory.getHistoryFor(pupil,competition);
            Map<Question, AnswerHistory> aList = AnswerHistory.getAnswerHistories(p);
            if(p == null || p.getQuestionSet() == null){
                flash("important", "nostats");
                return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
            }
            List<Question> lq = Set.getQuestions(p.getQuestionSet());


            //Excel opbouwen
            Workbook workbook = new XSSFWorkbook();
            addStatsToWorkbook(competition,workbook,pupil,lq, aList);

            byte[] bytes = null;
            try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                workbook.write(bos);
                bytes = bos.toByteArray();
            } catch (IOException e) {
                System.err.println("Error with downloading results file");
            }
            response().setHeader("Content-Disposition", "attachment; filename=Results.xlsx");
            return ok(bytes);
        }

        return ok();
    }

    public static Result downloadStatisticsForClass(long competitionId, long classId){
        Competition c = Competition.findById(competitionId);
        Class cl = Class.findClassById(classId);
        List<Pupil> lp;
        lp = Class.getPupils(cl);
        int numberOfParticipationHistories = 0;
        Workbook w = new XSSFWorkbook();
        Map<Pupil, ParticipationHistory> phmap = new HashMap<>();
        for(Pupil pup : lp){
            ParticipationHistory p = ParticipationHistory.getHistoryFor(pup,c);
            if(p != null){
                phmap.put(pup,p);
                numberOfParticipationHistories++;
            }
        }
        if(numberOfParticipationHistories <1){
            flash("important",LangMessages.get("nostats"));
            return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
        }
        for(Pupil pup: lp){
            ParticipationHistory ph = phmap.get(pup);
            Map<Question, AnswerHistory> aList = AnswerHistory.getAnswerHistories(ph);
            if(ph!= null){
                List<Question> lq = Set.getQuestions(ph.getQuestionSet());
                addStatsToWorkbook(c,w,pup,lq,aList);
            }
        }

        byte[] bytes = null;
        try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
            w.write(bos);
            bytes = bos.toByteArray();
        } catch (IOException e) {
            System.err.println("Error with downloading results file");
        }
        response().setHeader("Content-Disposition", "attachment; filename=Results.xlsx");
        return ok(bytes);
    }

    public static Result downloadStatistics(long competitionId){
        Competition c = Competition.findById(competitionId);
        List<Class> cl = c.getParticipatingClasses(Application.getCurrentlyLoggedInTeacher().bebrasId);
        if(c.isOpen != 2 && c.compType == CompetitionType.OFFICIAL){
            flash("important",LangMessages.get("closeFirst"));
             return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
        }
        if(cl.size() <2){
            List<Pupil> lp = new ArrayList<>();
            for(Class clazz : cl){
                lp.addAll(Class.getPupils(clazz));
            }
            int i=0;
            Workbook w = new XSSFWorkbook();
            for(Pupil pup : lp){
                ParticipationHistory p = ParticipationHistory.getHistoryFor(pup,c);
                Map<Question, AnswerHistory> aList = AnswerHistory.getAnswerHistories(p);
                if(p != null){
                    List<Question> lq = Set.getQuestions(p.getQuestionSet());
                    i++;
                    addStatsToWorkbook(c,w,pup,lq,aList);
                }

            }
            if(i<1){
                flash("important",LangMessages.get("nostats"));
                return redirect(routes.MonitorCompetitionController.monitorCompetition(competitionId));
            }
            byte[] bytes = null;
            try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                w.write(bos);
                bytes = bos.toByteArray();
            } catch (IOException e) {
                System.err.println("Error with downloading results file");
            }
            response().setHeader("Content-Disposition", "attachment; filename=Results.xlsx");
            return ok(bytes);
        }
        else {
            return ok(downloadStatistics.render(cl,c));
        }
    }

    private static void addStatsToWorkbook (Competition c,Workbook w, Pupil p, List<Question> lq, Map<Question, AnswerHistory> aList){
        //Todo: i18n
        int numberCorrect = 0;
        int numberWrong = 0;
        Sheet s = w.createSheet(p.firstName + " " + p.lastName);
        Row r1 = s.createRow(0);
        Cell c1 = r1.createCell(0);
        c1.setCellValue(c.getTitle());
        Row r2 = s.createRow(1);
        Cell c2 =  r2.createCell(0);
        c2.setCellValue(LangMessages.get("questionTitle"));
        Cell c3 =  r2.createCell(1);
        c3.setCellValue(LangMessages.get("answer"));
        Cell c4 =  r2.createCell(2);
        c4.setCellValue(LangMessages.get("correct"));

        for(int i=0;i<lq.size();i++) {
            Question q = lq.get(i);
            AnswerHistory ah = aList.get(q);
            if(ah != null){
                Row r = s.createRow(i+2);
                Cell c5 = r.createCell(0);
                c5.setCellValue(q.getTitle());
                Cell c6 = r.createCell(1);
                c6.setCellValue(ah.givenAnswer);
                Cell c7 = r.createCell(2);
                c7.setCellValue(q.isCorrectAnswer(ah.givenAnswer));
                if(q.isCorrectAnswer(ah.givenAnswer)){
                    numberCorrect++;
                }
                else {
                    numberWrong++;
                }
            }
        }

        if(lq.size() > 0){
            Row r = s.createRow(2+lq.size());
            Cell c8 = r.createCell(0);
            c8.setCellValue("#" + LangMessages.get("correct"));
            Cell c9 = r.createCell(1);
            c9.setCellValue(numberCorrect);
            Cell c10 = r.createCell(2);
            c10.setCellValue("#" + LangMessages.get("wrong"));
            Cell c11 = r.createCell(3);
            c11.setCellValue(numberWrong);
            Cell c12 = r.createCell(4);
            c12.setCellValue("%"+ LangMessages.get("correct"));
            Cell c13 = r.createCell(5);
            c13.setCellValue(numberCorrect/lq.size());
        }
    }

    public static Result showRightAndWrong(Long cId, String bebrasId){
        Pupil p = Pupil.getPupil(bebrasId);
        Competition c = Competition.findById(cId);
        ParticipationHistory ph = ParticipationHistory.getHistoryFor(p,c);
        Map<Question,AnswerHistory> mapah = AnswerHistory.getAnswerHistories(ph);
        int numberCorrect=0;
        int numberWrong=0;
        for(Question q :mapah.keySet()){
            AnswerHistory ah = mapah.get(q);
            if(q.isCorrectAnswer(ah.givenAnswer)){
                numberCorrect++;
            }
            else{
                numberWrong++;
            }
        }
        boolean isViewAble = true;
        if(c.isOpen != 2 && c.compType == CompetitionType.OFFICIAL){
            isViewAble = false;
        }
        return ok(competitionStats.render(numberCorrect, numberWrong,isViewAble));
    }

    public static Result pupilDownloadStatistics(Long historyId){
        //Eigen puntenverdeling berekenen
        ParticipationHistory ph = ParticipationHistory.findById(historyId);
        int numberCorrect = Math.calcCorrect(ph);
        int numberWrong = Math.calcWrong(ph);
        //Vergelijking andere studenten berekenen

        List<ParticipationHistory> allPh = ParticipationHistory.getHistoryFor(ph.competition);
        if(allPh.size() == 0){
            //TODO implement error
        }
        int numberAvgCorrect = Math.calcAvgCorrect(allPh);
        int numberAvgWrong = Math.calcAvgWrong(allPh);
        return ok(viewStatsCompetition.render(numberCorrect,numberWrong,numberAvgCorrect, numberAvgWrong,ph.competition.getTitle()));
    }

    public static Result getStatsForQuestion(Long setId, Long questionId){
        Set s = Set.findById(setId);
        Question q = Question.getQuestion(questionId);
        List<ParticipationHistory> allPh = ParticipationHistory.getHistoryFor(s);
        List<Integer> points = new ArrayList<>();
        int correctAnswerPoints = s.getCorrectPoints(q);
        int wrongAnswerPoints = s.getIncorrectPoints(q);
        int correctNumber = 0;
        int wrongNumber = 0;
        for(ParticipationHistory ph: allPh){
            if(q.isCorrectAnswer(ph.getGivenAnswer(q))){
                correctNumber ++;
            }
            else{
                wrongNumber ++;
            }
        }
        return ok(questionStats.render(correctAnswerPoints, wrongAnswerPoints, correctNumber, wrongNumber,q));
    }

    @Security.Authenticated(SecuredTeacher.class)
    public static Result viewStatsForClass(Long classId){
        Class clazz = Class.findClassById(classId);
        List<ParticipationHistory> pList = ParticipationHistory.getAllHistory(Class.getPupils(clazz));
        if(pList.size()<1){
            flash("important",LangMessages.get("nostats"));
            return redirect(routes.ProfilesController.viewClass(classId));
        }
        Map<Competition,List<Pupil>> mp = new HashMap<>();
        for(ParticipationHistory ph : pList){
            Competition comp = ph.getCompetition();
            if(mp.containsKey(comp)){
                mp.get(comp).add(ph.participant);
            }
            else {
                List<Pupil> newList = new ArrayList<>();
                newList.add(ph.participant);
                mp.put(comp, newList);
            }
        }

        List<Competition> l = new ArrayList<>(mp.keySet());
        return ok(viewAllStatsForClass.render(l,clazz));
    }

    @Security.Authenticated(SecuredOrganizer.class)
    public static Result viewTop20(){
        List<ParticipationHistory> allPh = ParticipationHistory.getCompetitionStats(CompetitionType.OFFICIAL);
        Collections.sort(allPh, new Comparator<ParticipationHistory>() {
            public int compare(ParticipationHistory a, ParticipationHistory b) {
                return a.getTotalPoints() - b.getTotalPoints();
            }
        });
        List<ParticipationHistory> top = new ArrayList<>();
        for(int i=0;i<java.lang.Math.min(allPh.size(), 20);i++){
            top.add(allPh.get(i));
        }
        return ok(top20.render(top));
    }

    public static class Math{
        public static int calcAvgCorrect(List<ParticipationHistory> allPh){
            int score=0;
            for(ParticipationHistory ph : allPh){
                score+=calcCorrect(ph);
            }
            return score/allPh.size();
        }
        public static int calcAvgWrong(List<ParticipationHistory> allPh){
            int score=0;
            for(ParticipationHistory ph : allPh){
                score+=calcWrong(ph);
            }
            return score/allPh.size();
        }

        public static int calcCorrect(ParticipationHistory ph ) {
            Map<Question,AnswerHistory> mapah = AnswerHistory.getAnswerHistories(ph);
            int numberCorrect=0;
            for(Question q :mapah.keySet()){
                AnswerHistory ah = mapah.get(q);
                if(q.isCorrectAnswer(ah.givenAnswer)){
                    numberCorrect++;
                }
            }
            return numberCorrect;
        }
        public static int calcWrong(ParticipationHistory ph ) {
            Map<Question,AnswerHistory> mapah = AnswerHistory.getAnswerHistories(ph);
            int numberWrong=0;
            for(Question q :mapah.keySet()){
                AnswerHistory ah = mapah.get(q);
                if(!q.isCorrectAnswer(ah.givenAnswer)){
                    numberWrong++;
                }
            }
            return numberWrong;
        }
    }

    public static class showStats {
        @Constraints.Required
        public String pupil;
    }
}
