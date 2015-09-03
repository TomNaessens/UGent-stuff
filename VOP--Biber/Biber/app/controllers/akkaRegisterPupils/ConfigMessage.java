package controllers.akkaRegisterPupils;

import java.io.File;

import models.Teacher;

/**
 * Message sent from Master to Child for starting a new job
 */
public class ConfigMessage {

    private String config;
    
    private String filename; 
    private File file;
    private String schoolAndId;
    private Teacher teacher;
    
    public ConfigMessage(String config, String filename, File file, String schoolAndId, Teacher teacher) {
        this.config = config;
        this.filename = filename;
        this.file = file;
        this.schoolAndId = schoolAndId;
        this.teacher = teacher;
    }
    
    public String getConfig() {
        return config;
    }
    
    public File getFile() {
        return file;
    }
    
    public String getSchoolAndId() {
        return schoolAndId;
    }
    
    public String getFilename() {
        return filename;
    }

    public Teacher getTeacher() {
        return teacher;
    }
    
}
