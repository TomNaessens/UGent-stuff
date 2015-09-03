package controllers;


import models.*;
import models.Class;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import play.mvc.Controller;
import play.mvc.Result;

import java.io.*;
import java.util.List;

import views.html.teacher.localCompetitionsClass;

public class WriteResultsToFile extends Controller {

    /**
     *  Add the results of a local competition for a class to a sheet in a given excel workbook.
     *  @param language The language for the title, can be null, in that case, default will be selected.
     * @param cl  The class
     * @param comp The competition
     * @param wb  The excel workbook
     * @return  The excel workbook with the class results.
     */
    public Workbook resultsToexcel(models.Class cl, Competition comp, Set set, Workbook wb, Language language) {

        Sheet s = wb.createSheet(cl.name);
        Row r = null;
        Cell c = null;

        /*Create first row*/
        r = s.createRow(0);
        c = r.createCell(0);
        c.setCellValue("Results");

        /*Create second row*/
        r = s.createRow(1);
        c = r.createCell(0);
        c.setCellValue("Competition:");
        c = r.createCell(1);
        if (comp.getTitle(language)!=null) {
            c.setCellValue(comp.getTitle(language));
        } else if (comp.getTitle()!=null){
            c.setCellValue(comp.getTitle());
        }
        c = r.createCell(2);
        c.setCellValue("Level:");
        c = r.createCell(3);
        c.setCellValue((cl.level).toString());


        /*Create third row*/
        r = s.createRow(2);
        c = r.createCell(0);
        c.setCellValue("First Name");
        c = r.createCell(1);
        c.setCellValue("Family Name");
        c = r.createCell(2);
        c.setCellValue("BebrasId");
        c = r.createCell(3);
        c.setCellValue("Points");

        List<Pupil> list = Pupil.findPupilsFromClass(cl);
        int row = 3;
        for (Pupil p: list) {
            r = s.createRow(row);
            c = r.createCell(0);
            c.setCellValue(p.firstName);
            c = r.createCell(1);
            c.setCellValue(p.lastName);
            c = r.createCell(2);
            c.setCellValue(p.bebrasId);
            c = r.createCell(3);
            ParticipationHistory history = ParticipationHistory.getHistoryFor(p, comp,  set);
            if (history!=null) {
                int totalPoints= history.getTotalPoints();
                c.setCellValue(totalPoints);
            } else {
                c.setCellValue("Not Participated");
            }
            row++;
        }

        for (int i=0; i<row; i++){
            s.autoSizeColumn(i);
        }

        return wb;
    }

    public String resultsToCsv(models.Class cl, Competition comp, Set set, Language language){
        String file;
        if(comp.getTitle(language)!=null) {
            file = "Results\nCompetition:,"+comp.getTitle(language)+",Level:,"+(cl.level).toString()+"\n";
        } else if (comp.getTitle()!=null) {
            file = "Results\nCompetition:,"+comp.getTitle()+",Level:,"+(cl.level).toString()+"\n";
        } else{
            file = "Results\nCompetition:,_,Level:,"+(cl.level).toString()+"\n";
        }
        file = file + "First Name, Family Name, BebrasId, Points\n";
        List<Pupil> list = Pupil.findPupilsFromClass(cl);
        for (Pupil p: list) {
            ParticipationHistory history = ParticipationHistory.getHistoryFor(p, comp,  set);
            if(history!=null){
                int totalPoints= history.getTotalPoints();
                file = file + p.firstName+","+p.lastName+","+p.bebrasId+","+totalPoints+"\n";
            } else {
                file = file + p.firstName+","+p.lastName+","+p.bebrasId+",_\n";
            }
        }
        return file;
    }

    public static Result viewRecentCompetitions(Long id){
        Class cl = Class.findClassById(id);
        return ok(localCompetitionsClass.render(cl.getFinishedCompetitions(), cl));
    }

    /**
     *
     * @param idComp The id of the competition
     * @param idClass  The id of the class
     * @param type  1: xls 2:xlsx 3:csv
     * @return
     */
    public static Result downloadResults(Long idComp, Long idClass, Long type) {
        WriteResultsToFile ob = new WriteResultsToFile();
        Class cl = Class.findClassById(idClass);
        Competition comp = Competition.findById(idComp);
        Set set = comp.questionSets.get(cl.level);
        byte[] bytes = null;

        /*excel files*/
        if (type==1 || type == 2) {
            Workbook wb;
            if(type==1) {
                wb = new HSSFWorkbook();
                response().setHeader("Content-Disposition", "attachment; filename=Results.xls");
            } else {
                wb = new XSSFWorkbook();
                response().setHeader("Content-Disposition", "attachment; filename=Results.xlsx");
            }
            wb = ob.resultsToexcel(cl, comp, set, wb, Language.ENGLISH);
            try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                wb.write(bos);
                bytes = bos.toByteArray();
            } catch (IOException e) {
                System.err.println("Error with downloading results file");
            }

        } else {
            /*Csv file*/
            String file;
            file = ob.resultsToCsv(cl, comp, set, Language.ENGLISH);
            try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                bos.write(file.getBytes());
                bytes = bos.toByteArray();
            } catch (IOException e) {
                System.err.println("Error with downloading results file");
            }
            response().setHeader("Content-Disposition", "attachment; filename=Results.csv");
        }


        return ok(bytes);
    }

}
