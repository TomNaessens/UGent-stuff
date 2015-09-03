package controllers.akkaRegisterPupils;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import javax.persistence.OptimisticLockException;

import models.Class;
import models.Person;
import models.Pupil;
import models.School;
import models.Teacher;

import org.apache.commons.mail.EmailException;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.joda.time.DateTime;
import org.joda.time.format.DateTimeFormat;
import org.joda.time.format.DateTimeFormatter;

import utils.LangMessages;
import utils.Mail;
import akka.actor.UntypedActor;
import au.com.bytecode.opencsv.CSVReader;
import au.com.bytecode.opencsv.CSVWriter;

import com.avaje.ebean.Ebean;

public class RegisterChildWorker extends UntypedActor {

    /**
     * Constant with the current amount of columns in the sheet asking for data
     */
    private static final int COLUMNS_IN_SHEET = 7;
    
    private int numberOfRowsDone=0;
    private int totalRows;
    private boolean errorWhileParsing = false;
    private Teacher currentlyLoggedInTeacher;
    
    private CSVWriter writer;
    
    // Fill these lists with temporary objects. Only save them when everything ok.
    private ArrayList<Pupil> temporaryRegisteredPupils = new ArrayList<Pupil>();
    private ArrayList<Class> temporaryUpdatedClasses = new ArrayList<Class>();
    
    /**
     * Called when this child worker receives a message. The only messages he receives are
     * ConfigMessages. This message tells this worker to start handling the file.
     */
    @Override
    public void onReceive(Object message) throws Exception {
        if (message instanceof ConfigMessage) {
            ConfigMessage configMessage = (ConfigMessage)message;
            this.currentlyLoggedInTeacher = configMessage.getTeacher();
            handleUpload(configMessage.getFile(),configMessage.getFilename(),configMessage.getSchoolAndId());          
        } else
            unhandled(message);    
    }
    
    
    /**
     * Expects a file. Determines the extension (supported are xs, xslx and
     * csv) and parses the file accordingly. Parsing consists of registering new
     * pupils and possibly create new classes if they don't already exist.
     * 
     * @param filename
     * @param file
     * @param schoolAndId of the form 'id - schoolname'
     */
    private void handleUpload(File file, String filename, String schoolAndId) {
     // TODO Atm basic extension finder -> implement more advanced one if
        // necessary
        String extension = "";
        long schoolId;
        int i = filename.lastIndexOf('.');
        if (i > 0) {
            extension = filename.substring(i + 1);
        }
        i = schoolAndId.indexOf('-');
        schoolId = Long.parseLong(schoolAndId.substring(0, i - 1));
        School school = School.findSchool(schoolId);
        if (extension.equals("xls") || extension.equals("xlsx")) {
            parsePupilsExcelFile(file, extension, school);
        }
        else if (extension.equals("csv")) {
            parsePupilsCSVFile(file, school, filename);
        }
        else{
            tellErrorToParent(LangMessages.get("registerPupils.filetypeNotSupported"));
        }
        tellProgressToParent(100);
    }   
    
    /**
     * First Method called for parsing a csv file. Iterates over the lines, catches errors, writes new file to send by mail, etc..
     * @param f, an uploaded CSV file
     * @param school
     * @param filename
     */
    private void parsePupilsCSVFile(File f, School school, String filename){
        try {
            CSVReader reader = new CSVReader(new FileReader(f));
            List<String[]> lines = reader.readAll();
            Iterator<String[]> it = lines.iterator();
            reader.close();
            File fileToSend = new File(filename);
            writer = new CSVWriter(new FileWriter(fileToSend));
            totalRows = lines.size();
            boolean parseClass = false;
            String [] nextLine; //ignore first line because this is defining format TODO: what if they don't use this line..??
            Class classToUploadFor = null;
            int year = DateTime.now().getYear();
            if (DateTime.now().getMonthOfYear() < 9) // so when adding a class in january 2013, year should be 2012                                      
                year--;
            try{
                while ((nextLine = it.next()) != null) {
                    if(nextLine[0].toLowerCase().contains("class")){ //TODO: better check.. Language check, just check if 3 column is empty etc etc
                        classToUploadFor = determineClassToUploadFor(nextLine[1],nextLine[3],year , school);
                        if (!classToUploadFor.teacher.bebrasId.equals(currentlyLoggedInTeacher.bebrasId)) {
                            tellErrorToParent(LangMessages.get("registerPupils.classesNotOwnedByTeacher",nextLine[1]));
                            parseClass = false;
                        } else {
                            temporaryUpdatedClasses.add(classToUploadFor);
                            parseClass = true;
                        }
                        writer.writeNext(nextLine);
                    }
                    else if(parseClass){ //assuming row for a pupil and parse it only when the class is valid
                        if(nextLine[0].equals("")) continue;
                        Pupil pupil;
                        try {
                            pupil = parsePupilRow(nextLine, classToUploadFor);
                            handleParsedPupil(pupil, nextLine[COLUMNS_IN_SHEET-1]);
                            insertBebrasIdAndPassword(nextLine,pupil);
                        } catch (Exception e) {
                            if(e instanceof IllegalArgumentException || e instanceof NullPointerException){
                                handleEnumError(e);
                            }else{
                                tellErrorToParent(e.toString());
                                e.printStackTrace();
                            }
                        } 
                    }
                }
            }
            catch(NoSuchElementException e){}
            writer.close();
            if(!errorWhileParsing)
                sendMailContainingLoginDetails(fileToSend); //error can happen here, so only save when also here no errors found
            fileToSend.delete();
            if (!errorWhileParsing) {
                Ebean.save(temporaryRegisteredPupils);
                Ebean.save(temporaryUpdatedClasses); 
            }
        } catch (IOException e)  {
            // TODO Auto-generated catch block
            e.printStackTrace();
            tellErrorToParent(e.toString());
        }
    }


    /**
     * @param file, an uploaded excel file
     * @param school, necessary for assigning new classes
     */
    private void parsePupilsExcelFile(File f, String extension,School school) {
        try {
            FileInputStream fin = new FileInputStream(f);
            Workbook workbook;
            if (extension.equals("xls"))
                workbook = new HSSFWorkbook(fin);
            else {
                workbook = new XSSFWorkbook(fin);
            }
            totalRows = determineTotalRows(workbook);
            for (int i = 0; i < workbook.getNumberOfSheets(); i++) {
                parseExcelSheet(workbook.getSheetAt(i), school);
            }
            if(!errorWhileParsing)
                sendMailContainingLoginDetails(workbook, extension); //error can happen here, so only save when also here no errors found
            if (!errorWhileParsing) {
                Ebean.save(temporaryRegisteredPupils);
                Ebean.save(temporaryUpdatedClasses);
            }
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            tellErrorToParent(e.toString());
        }
    }
    
    /**
     * Parses given excel sheet. Adds class to school and registers pupils in sheet.
     * @param sheet, Excel sheet to parse
     * @param school
     * @param temporaryUpdatedClasses
     * @param temporaryRegisteredPupils
     * @return Null if parsing succeeded. Returns redirect result (+ error message in flash scope) if parsing failed.
     */
    public void parseExcelSheet(Sheet sheet, School school) {
        String className = sheet.getSheetName();
        String level = sheet.getRow(1).getCell(1).getStringCellValue();
        int beginYear = (int) sheet.getRow(0).getCell(1).getNumericCellValue();
        Class classToUploadFor = determineClassToUploadFor(className,level, beginYear, school);
        // If class is not one of teacher's, don't parse it and let teacher know that he should contact responsible teacher
        if (!classToUploadFor.teacher.bebrasId.equals(currentlyLoggedInTeacher.bebrasId)) {
            tellErrorToParent(LangMessages.get("registerPupils.classesNotOwnedByTeacher",className));
        } else {
            temporaryUpdatedClasses.add(classToUploadFor);
            Row row = sheet.getRow(2);
            Cell passCell = row.getCell(COLUMNS_IN_SHEET);
            passCell = row.createCell(COLUMNS_IN_SHEET);
            passCell.setCellValue("Password");
            for(int rowNum = 3; rowNum < 50 ; rowNum++){
                row = sheet.getRow(rowNum);
                if(row == null || row.getCell(0, Row.RETURN_BLANK_AS_NULL) == null)
                    continue;
                Pupil pupil;
                try {
                    pupil = parse_pupil_row(row, classToUploadFor);
                    handleParsedPupil(pupil, row.getCell(COLUMNS_IN_SHEET-1,Row.CREATE_NULL_AS_BLANK).getStringCellValue());
                    insertBebrasIdAndPasswordIntoRow(row, pupil); //inserts generated id and password in the row of the pupil 
                } catch (Exception e) {
                    if(e instanceof IllegalArgumentException || e instanceof NullPointerException){
                        handleEnumError(e);
                    }else{
                        tellErrorToParent(e.toString());
                        e.printStackTrace();
                    }
                }
            }
        }
    }
    
    
    /**
     * Parses row containing data of one pupil. Can be used by both HSSF and
     * XSSF Does not saves any of the pupils. New pupils only saved to DB when
     * sheet fully correct.
     * 
     * @param row, a row containing data of one pupil
     * @param newClass, the new class the pupil will be joining
     * @return Pupil object, null if parsing failed.
     * @throws Exception 
     */
    public Pupil parse_pupil_row(Row row, Class classToUploadFor) throws Exception {
        Object[] pupilAttributes = new Object[COLUMNS_IN_SHEET];
        for (int cn = 0; cn < COLUMNS_IN_SHEET; cn++) {
            Cell c = row.getCell(cn, Row.RETURN_BLANK_AS_NULL);
            if (cn == 5) { // DATE
                try {
                    pupilAttributes[cn] = new DateTime(c.getDateCellValue());
                } catch (Exception e) {
                    tellErrorToParent(LangMessages.get("registerPupils.dateFormatNotCorrect"));
                    pupilAttributes[cn] = DateTime.now(); // just a working value not to cause nullpointers                                 
                }
            } else {
                if(c != null)
                    pupilAttributes[cn] = c.getStringCellValue();
            }
        }
        // Check for existing bebrasId
        if (pupilAttributes[COLUMNS_IN_SHEET - 1] != null) {
            Pupil existingPupil = Pupil.getPupil((String) pupilAttributes[COLUMNS_IN_SHEET-1]);
            if (existingPupil == null) {
                return null; // return null, calling method handles error.
            } else {
                // TODO update other values of found pupil?
                existingPupil.currentClass = classToUploadFor;
                return existingPupil;
            }
        } else {
            DateTime birthday = (DateTime) pupilAttributes[5];
            String email = (String) pupilAttributes[2];
            Pupil p = Pupil.createPupilAndAssignClass(email,
                    (String) pupilAttributes[0], (String) pupilAttributes[1],
                    ((String) pupilAttributes[3]), (String) pupilAttributes[4],
                    birthday.getDayOfMonth(), birthday.getMonthOfYear(), birthday.getYear(),
                    classToUploadFor);
            generateCorrectIdIfNeeded(p);
            return p;
        }
    }
    
    /**
     * Parses a (currently only) csv row and returns a new or found Pupil. SAVING TO DB HAPPENS UPSTREAM
     * TODO: use this method also for excel parsing
     * @param pupilAttributes
     * @param classToUploadFor
     * @return the newly created or found pupil.
     * @throws Exception 
     */
    private Pupil parsePupilRow(String[] pupilAttributes, Class classToUploadFor) throws Exception{
        // Check for existing bebrasId
        if (!pupilAttributes[COLUMNS_IN_SHEET - 1].equals("")) {
            Pupil existingPupil = Pupil.getPupil((String) pupilAttributes[COLUMNS_IN_SHEET-1]);
            if (existingPupil == null) {
                return null; // return null, calling method handles error.
            } else {
                // TODO update other values of found pupil?
                existingPupil.currentClass = classToUploadFor;
                return existingPupil;
            }
        } else {
            DateTimeFormatter formatter = DateTimeFormat.forPattern("dd/MM/yyyy");
            DateTime birthday;
            try{
                birthday = formatter.parseDateTime(pupilAttributes[5]);
            }
            catch(Exception e){
                tellErrorToParent(LangMessages.get("registerPupils.dateFormatNotCorrect"));
                birthday = null;
            }
            Pupil p = Pupil.createPupilAndAssignClass(pupilAttributes[2],
                    pupilAttributes[0],pupilAttributes[1],
                    pupilAttributes[3],pupilAttributes[4],
                    birthday.getDayOfMonth(), birthday.getMonthOfYear(), birthday.getYear(),
                    classToUploadFor);
            generateCorrectIdIfNeeded(p);
            return p;
        }
    }
    
    /**
     * Handler for a found or newly created pupil. When the pupil is null, the bebarsId column was filled in, but corresponding pupil could not be found.
     * Also checks if email correct and not already existing in the database. Also reports progress to parent!
     * @param pupil
     * @param bebrasId
     */
    private void handleParsedPupil(Pupil pupil, String bebrasId){
        if (pupil != null) {
            Person temp = Person.findPersonByEmail(pupil.email);
            if(pupil.email != null && !pupil.email.equals("") && !Person.emailCorrect(pupil.email)){
                tellErrorToParent(LangMessages.get("registerPupils.emailNotCorrect",pupil.email));
            }
            if(temp != null && temp.email != null && Pupil.findPupilByBebrasID(pupil.bebrasId) == null){ //third check, because it is possible bebrasId field was filled in and pupil thus already exists
                if(temp instanceof Pupil){ //the existing email was of a pupil, so give teacher the corresponding bebrasId
                    tellErrorToParent(LangMessages.get("registerPupils.emailExistsPupil1", pupil.email) + LangMessages.get("registerPupils.emailExistsPupil2",temp.bebrasId));
                }
                else{ //the existing email was not of a pupil..
                    tellErrorToParent(LangMessages.get("registerPupils.emailExists1", pupil.email ) + LangMessages.get("registerPupils.emailExists2"));
                }
            }
            temporaryRegisteredPupils.add(pupil);
        } else {
            tellErrorToParent(LangMessages.get("registerPupils.bebrasIdNotCorrect",bebrasId));
        }
        tellProgressToParent((++numberOfRowsDone * 100)/totalRows);
    }
    
    /**
     * Inserts the bebrasId and password of the given pupil in the given row.
     * @param row, containing already known data
     * @param p
     */
    private void insertBebrasIdAndPasswordIntoRow(Row row,Pupil p){
        if(p == null) return;
        Cell idCell = row.getCell(COLUMNS_IN_SHEET-1);
        Cell passCell = row.getCell(COLUMNS_IN_SHEET);
        if (idCell == null)
            idCell = row.createCell(COLUMNS_IN_SHEET-1);
        if (passCell == null)
            passCell = row.createCell(COLUMNS_IN_SHEET);
        idCell.setCellType(Cell.CELL_TYPE_STRING);
        passCell.setCellType(Cell.CELL_TYPE_STRING);
        idCell.setCellValue(p.bebrasId);
        passCell.setCellValue(p.firstPassword);
    }
    
    /**
     * Insert bebrasId and password in the correct row and writes it to the outputfile.
     * @param row, containing already known data
     * @param p
     */
    private void insertBebrasIdAndPassword(String[] row, Pupil p){
        String[] temp = new String[8];
        for(int i = 0; i < 6 ; i++){
            temp[i] = row[i];
        }
        temp[6] = p.bebrasId;
        temp[7] = p.firstPassword;
        writer.writeNext(temp);
    }
    
    /**
     * Given the name of the class and the school, it determines whether a new
     * class should be created for this school and returns the new or already
     * existing class.
     * 
     * @param className
     * @param level
     * @param school
     * @param beginyear
     * @return new or already existing class object
     */
    private Class determineClassToUploadFor(String className,String level, int beginYear, School school) {
        // Do not save yet, this happens in calling method when everything ok
        int year = DateTime.now().getYear();
        // so when adding a class in january 2013, year should be 2012
        if (DateTime.now().getMonthOfYear() < 9) {
            year--;
        }
        List<Class> classesOfSchool = Class.findSchoolClasses(school.id);
        Class classToUploadFor = null;
        for (Class c : classesOfSchool) {
            if (c.name.equals(className) && c.beginYear == year) {
                classToUploadFor = c;
                break;
            }
        }
        // Class doesn't exist yet
        if (classToUploadFor == null) {
            classToUploadFor = new Class(className, level, year, school,
                    currentlyLoggedInTeacher);
        }
        return classToUploadFor;
    }
    
    /**
     * Send mail with the login details of the uploaded pupils. To be used with excel workbook.
     * @param wb
     * @param extension
     */
    private void sendMailContainingLoginDetails(Workbook wb, String extension){
        try {
            FileOutputStream fileOut = new FileOutputStream("excelfile." +extension);
            wb.write(fileOut);
            fileOut.close();
            File file = new File("excelfile." +extension);
            String email = currentlyLoggedInTeacher.email;
            Mail.sendMailWithAttachment(email, LangMessages.get("registerPupils.email.subject"), LangMessages.get("registerPupils.email.message"), file);
            file.delete();
        } catch (Exception e) {
            if(e instanceof EmailException){
                e.printStackTrace();
                tellErrorToParent(LangMessages.get("registerPupils.error.mail"));
            }
            else{
                tellErrorToParent(e.toString());
            }
        }  
    }
    
    /**
     * Send mail with the login details of the uploaded pupils. Currently used for CSV files.
     * @param f
     */
    private void sendMailContainingLoginDetails(File f){
        try {
            Mail.sendMailWithAttachment(currentlyLoggedInTeacher.email, LangMessages.get("registerPupils.email.subject"), LangMessages.get("registerPupils.email.message"), f);
        } catch (EmailException e) {
            if(e instanceof EmailException){
                e.printStackTrace();
                tellErrorToParent(LangMessages.get("registerPupils.error.mail"));
            }
            else{
                tellErrorToParent(e.toString());
            }
        }
    }
    
    /**
     * Determines the total amount of rows in the workbook. Used for reporting progress to parent.
     * @param workbook
     * @return total amount of rows
     */
    private int determineTotalRows(Workbook workbook) {
        int totalrows = 0;
        for (int i = 0; i < workbook.getNumberOfSheets(); i++) {
            totalrows += workbook.getSheetAt(i).getLastRowNum();
        }
        return totalrows;
    }
    
    /**
     * Handles errors made in the files on the enums: Language, Level, Gender, ...
     * @param e
     */
    private void handleEnumError(Exception e) {
        String error = e.toString();
        String value = error.substring(error.lastIndexOf('.') + 1);
        String errorMessage = error;
        if(e instanceof NullPointerException){
            errorMessage = LangMessages.get("registerPupils.error.cellEmpty");
        }
        if(error.toLowerCase().contains("language")){
            errorMessage = LangMessages.get("registerPupils.error.enum.language",value);
        }
        if(error.toLowerCase().contains("level")){
            errorMessage = LangMessages.get("registerPupils.error.enum.level", value);
        }
        if(error.toLowerCase().contains("gender")){
            errorMessage = LangMessages.get("registerPupils.error.enum.gender", value);
        }
        tellErrorToParent(errorMessage);
    }
    
    /**
     * Checks if the current assigned bebrasId isn't already contained in the DB and/or temporary list and generates a new one
     * accordingly.
     * @param pupil
     */
    private void generateCorrectIdIfNeeded(Pupil pupil){
        for(Pupil p: temporaryRegisteredPupils){
            if(p.bebrasId.equals(pupil.bebrasId)){
                pupil.bebrasId = generateNewId(pupil.firstName,pupil.lastName);
                return;
            }
        }
    }
    
    /**
     * Generate a new bebrasId which is not already in the database or in the temporary list.
     * @param firstName
     * @param lastName
     * @return
     */
    private String generateNewId(String firstName, String lastName){
        String bebrasId = (firstName.charAt(0) + lastName).toLowerCase().replaceAll("\\s","");
        while(Person.getPerson(bebrasId)!= null || tempContainsId(bebrasId)){
            int rand = (int) (Math.random()*10000); //number can be decreased or increased if necessary
            bebrasId = (firstName.charAt(0) + lastName + rand).toLowerCase().replaceAll("\\s","");
        }
        return bebrasId;
    }
    
    /**
     * Check if the temporary list contains this id
     * @param bebrasId
     * @return
     */
    private boolean tempContainsId(String bebrasId){
        for(Pupil p: temporaryRegisteredPupils){
            if(p.bebrasId.equals(bebrasId))
                return true;
        }
        return false;
    }
    
    /**
     * Tell the akka parent the progress of parsing the file
     * @param progress
     */
    public void tellProgressToParent(int progress){
        this.context().parent().tell(new StatusUpdate(progress),getSelf());
    }
    
    /**
     * Tell the parent that an error has occured. Parent will send this to view.
     * @param error
     */
    public void tellErrorToParent(String error){
        this.errorWhileParsing = true;
        this.context().parent().tell(new ErrorUpdate(error),getSelf());
    }

}
