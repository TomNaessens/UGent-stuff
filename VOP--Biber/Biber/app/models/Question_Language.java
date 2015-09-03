package models;

import java.util.Random;

import play.db.ebean.Model;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.ManyToOne;

@Entity
public class Question_Language extends Model {

    // TODO: figure out if we can somehow remove the id? This class is actually a relation, not an entity...
    @Id
    public Long id;

    // For every language we need to know the title of the question
    public String title;

    // Filename of answer file
    public String questionFile;
    // Random question file name to deny random access
    public String randomQuestionFile;
    
    //Random feedback file name to deny random access
    public String randomFeedbackFile;
    
    // Filename of feedback file
    public String feedbackFile;

    public Language language;

    public Question_Language(String title, String questionFile, String feedbackFile, Language language) {
        this.title = title;
        this.questionFile = questionFile;
        this.feedbackFile = feedbackFile;
        this.language = language;
    }

	public Question_Language() {
		
	}
	
	public String generateRandomString() {
		String characters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
		String out = "";
		int len = 15;
		Random random = new Random();
		for(int i = 0; i < len; i++) {
			out+= characters.charAt(random.nextInt(characters.length()));
		}
		return out;
	}
	
	public void generateRandomQuestionFileName() {
		randomQuestionFile = generateRandomString();
		while(randomQuestionFile.equals(randomFeedbackFile)) {
			randomQuestionFile = generateRandomString();
		}
		randomQuestionFile += "_" + language.getOfficialCode() + ".html";
	}
	
	public void generateRandomFeedbackFileName() {
		randomFeedbackFile = generateRandomString();
		while(randomFeedbackFile.equals(randomQuestionFile)) {
			randomFeedbackFile = generateRandomString();
		}
		randomFeedbackFile += "_" + language.getOfficialCode() + ".html";
	}

}
