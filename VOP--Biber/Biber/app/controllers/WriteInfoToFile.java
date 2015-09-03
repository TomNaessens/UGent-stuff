package controllers;


import models.*;
import models.Class;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import play.data.DynamicForm;
import play.data.Form;
import play.data.validation.Constraints;
import play.mvc.Controller;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import org.joda.time.DateTime;
import play.mvc.Result;
import play.data.validation.Constraints.Required;

import utils.LangMessages;
import views.html.teacher.downloadClasses;

import static play.data.Form.form;

/**
 * Class for writing classes and schools to excel (xls and xlsx) and csv.
 *
 */

public class WriteInfoToFile extends Controller{

    /**
     * Add all classes from a given school to a given excel workbook.
     * @param school  The school
     * @param wb   The excel workbook
     * @return  The excel workbook with each class in a separate sheet.
     */
    public Workbook writeSchoolToexcel(School school, Workbook wb, boolean current) {
        List<Class> list;
        if (current) {
            list = Class.findSchoolClasses(school.id);
        } else {
            list = Class.findPreviousSchoolClasses(school.id);
        }
        for ( Class cl: list ) {
            wb = writeClassToexcel(cl, wb, current);
        }
        return wb;
    }

    /**
     *  Add a class to a given excel workbook.
     * @param cl  The class
     * @param wb  The excel workbook
     * @return  The excel workbook with the class in a separate sheet.
     */
    public Workbook writeClassToexcel(Class cl, Workbook wb, boolean current) {
        List<Pupil> list;
        if (current) {
            list = Pupil.findPupilsFromClass(cl);
        } else {
            list = Pupil.findPupilsFromPreviousClass(cl);
        }
        Sheet s = wb.createSheet(cl.name);
        Row r = null;
        Cell c = null;

        /*Create first row*/
        r = s.createRow(0);
        c = r.createCell(0);
        c.setCellValue("Year");
        c = r.createCell(1);
        c.setCellValue(DateTime.now().getYear());

        /*Create second row*/
        r = s.createRow(1);
        c = r.createCell(0);
        c.setCellValue("Level");
        c = r.createCell(1);
        c.setCellValue((cl.level).toString());

        /*Create third row*/
        r = s.createRow(2);
        c = r.createCell(0);
        c.setCellValue("First Name");
        c = r.createCell(1);
        c.setCellValue("Family Name");
        c = r.createCell(2);
        c.setCellValue("Email");
        c = r.createCell(3);
        c.setCellValue("Gender");
        c = r.createCell(4);
        c.setCellValue("Language");
        c = r.createCell(5);
        c.setCellValue("Birthday");
        c = r.createCell(6);
        c.setCellValue("BebrasID");


        int row = 3;
        for (Pupil p: list) {
            r = s.createRow(row);
            c = r.createCell(0);
            c.setCellValue(p.firstName);
            c = r.createCell(1);
            c.setCellValue(p.lastName);
            c = r.createCell(2);
            if (p.email!=null){
                c.setCellValue(p.email);
            }
            c = r.createCell(3);
            if (p.gender!=null) {
                c.setCellValue(p.gender.toString());
            }
            c = r.createCell(4);
            if (p.language!=null) {
                c.setCellValue(p.language.toString());
            }
            c = r.createCell(5);
            if (p.dateOfBirth!=null) {
                c.setCellValue(p.dateOfBirth.getDayOfYear()+"/"+p.dateOfBirth.getDayOfMonth()+"/"+p.dateOfBirth.getYear());
            }
            c = r.createCell(6);
            c.setCellValue(p.bebrasId);
            row++;
        }

        for (int i=0; i<row; i++){
            s.autoSizeColumn(i);
        }
        return wb;
    }

    public String writeSchoolToCsv(School school, boolean current){
        String file="";
        List<Class> list = Class.findSchoolClasses(school.id);
        for ( Class cl: list ) {
            file = file + writeClassToCsv(cl, file, current);
            file = file + "\n\n-----------------------------------------\n\n";
        }
        return file;
    }

    public String writeClassToCsv(Class cl, String file, boolean current){
        List<Pupil> list;
        if (current) {
            list = Pupil.findPupilsFromClass(cl);
        } else {
            list = Pupil.findPupilsFromPreviousClass(cl);
        }
        String help;
        help = "Year,"+DateTime.now().getYear()+"\nLevel,"+(cl.level).toString()+"\n";
        help = help + "First Name, Family Name, Email, Gender, Language, Birthday, BebrasID";
        for (Pupil p: list) {
            help = help + p.firstName + ", "+ p.lastName;
            if (p.email!=null){
                help = help + ", "+ p.email;
            }else{
                help = help + ", ,";
            }
            if (p.gender!=null) {
                help = help + ", "+ p.gender;
            } else {
                help = help + ", ,";
            }
            if (p.language!=null) {
                help = help + ", "+ p.language;
            } else{
                help = help + ", ,";
            }
            if (p.dateOfBirth!=null) {
                help = help + ", "+ (p.dateOfBirth.getDayOfYear()+"/"+p.dateOfBirth.getDayOfMonth()+"/"+p.dateOfBirth.getYear());
            } else{
                help = help + ", ,";
            }
            help = help + ", "+p.bebrasId;

        }
        file = file + help;
        return file;
    }


    public static Result renderDownloadClasses(){
        Teacher t = Application.getCurrentlyLoggedInTeacher();
        return ok(downloadClasses.render(form(Download.class), t));
    }

    /**
     *
     * @return
     */
    public static Result downloadClasses() {
        WriteInfoToFile ob = new WriteInfoToFile();
        //DynamicForm requestData = myForm.bindFromRequest();
        Form<Download> myForm = Form.form(Download.class).bindFromRequest();
        if (myForm.hasErrors()) {
            Teacher t = Application.getCurrentlyLoggedInTeacher();
            return badRequest(downloadClasses.render(myForm, t));
        }
        String year = myForm.get().year;
        String school = myForm.get().school;
        Long idSchool = Long.parseLong(school);
        School sch = School.findSchool(idSchool);
        String type = myForm.get().type;
        Boolean current = false;
        if (year.equals("CURRENT")) {
            current = true;
        }
        byte[] bytes = null;

        //excel files
        if (type.equals("XLS") || type.equals("XLSX")) {
            Workbook wb;
            if(type.equals("XLS")) {
                wb = new HSSFWorkbook();
                response().setHeader("Content-Disposition", "attachment; filename=Results.xls");
            } else {
                wb = new XSSFWorkbook();
                response().setHeader("Content-Disposition", "attachment; filename=Results.xlsx");
            }
            wb = ob.writeSchoolToexcel(sch,wb,current);
            try (ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                wb.write(bos);
                bytes = bos.toByteArray();
            } catch (IOException e) {
                System.err.println("Error with downloading results file");
            }

        } else {
            //Csv file
            String file;
            file = ob.writeSchoolToCsv(sch, current);
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

    /**
     * Private class defining the fields of the activate account form
     */
    public static class Download {

        @Required
        public String year;
        @Required
        public String type;
        @Required
        public String school;

        public String validate(){
            return null;
        }

    }

}
