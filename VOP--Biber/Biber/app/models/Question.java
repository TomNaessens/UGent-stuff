package models;


import play.db.ebean.*;
import utils.AnswerChecker;
import utils.LangMessages;
import javax.persistence.*;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@Entity
public class Question extends Model implements Comparable<Question> {

    @Id
    public Long id;

    public String officialId;     // This is an optional field (can be null)
    public String author;

    public AnswerType answerType;
    public String answer;

    @ManyToOne
    public FileServer server;

    // A question can be written in multiple languages
    @OneToMany(cascade = CascadeType.ALL)
    @MapKey(name = "language")
    public Map<Language, Question_Language> questionLanguages;

    @Transient
    private AnswerChecker answerChecker = null;

    public static Finder<Long, Question> find = new Finder(Long.class, Question.class);

    // static properties
    public static final int QUESTION_INDEX = 0;
    public static final int FEEDBACK_INDEX = 1;


    public Question(String author,
                    AnswerType answerType, String answer,
                    FileServer server,
                    Map<Language, Question_Language> questionLanguages) {

        this(null, author, answerType, answer, server, questionLanguages);
    }
    public Question(){}

    public Question(String officialId, String author,
                    AnswerType answerType, String answer,
                    FileServer server,
                    Map<Language, Question_Language> questionLanguages) {

        this.officialId = officialId;
        this.author = author;
        this.answerType = answerType;
        this.answer = answer;
        this.server = server;
        this.questionLanguages = questionLanguages;

        this.save();
    }

    /**
     * Returns the title for this question in the given language
     *
     * @param language  The Language for which we want the title
     *
     * @return          Returns a String containing the title in
     *                  the specified language, or null in case
     *                  there is no title for the given language.
     */
    public String getTitle(Language language) {
        Question_Language ql = questionLanguages.get(language);

        if (ql != null)
            return ql.title;

        return null;
    }
    
	/**
	 * returns the title for this Question in the currently logged in user's preferred language.
	 * If that doesn't exist, it gives the title in the order given by the Language Enum
	 * 
	 * @return
	 */
	public String getTitle() {
			return getTitle(LangMessages.getLanguage(questionLanguages.keySet()));
	}

    /**
     * Method to find all questions in database
     * @return The list of questions
     */
    public static List<Question> getAllQuestions(){
          return find.all();
    }

    public static Question getQuestion(Long id){
        return find.byId(id);
    }

    /**
     * Returns the URLs to both the question page and the answer page in an array
     * for the given Language.
     * The element with index Question.QUESTION_INDEX contains the question URL, the element
     * with index Question.FEEDBACK_INDEX contains the answer URL.
     *
     * @param language  The Language for which we want the URLs
     *                  to the question and feedback page
     *
     * @return          Returns an URL[] which contains both the question
     *                  page and feedback page URL in case there exists question
     *                  and feedback URLs for the given Language.
     *                  Use Question.QUESTION_INDEX to index the element which contains
     *                  the question URL and Question.FEEDBACK_INDEX to get the
     *                  element which contains the feedback URL.
     *                  In case there are nog URLs for the given language,
     *                  null is returned.
     */
    public URL[] getURLs(Language language) {
        Question_Language ql = questionLanguages.get(language);

        if (ql == null)
            return null;

        URL[] urls = null;
        try {
            URL questUrl = ql.questionFile != null ? new URL(server.publicLink, id + "/" + ql.randomQuestionFile) : null;
            URL feedUrl = ql.feedbackFile != null ? new URL(server.publicLink, id + "/" + ql.randomFeedbackFile): null;

            urls = new URL[] { questUrl, feedUrl };
        } catch (MalformedURLException e) {
            // Shouldn't happen
        }

        return urls;
    }

    private URL getURL(Language language, int index) {
        URL[] urls = getURLs(language);

        return (urls == null) ? null : urls[index];
    }

    /**
     * Returns the URL to question page for the specified language
     *
     * @param language  The Language for which we want the URL
     *                  to the question page
     *
     * @return          Returns an URL to the question page in the
     *                  specified language, or null in case there is
     *                  no question page for the given language.
     */
    public URL getQuestionURL(Language language) {
        return getURL(language, Question.QUESTION_INDEX);
    }
    
    /**
     * Calls getQuestionURL(Language language) with language being the preferred language of the user
     * and if that doesn't exist, the first url that does exist in order as specified by the Language Enum
     * @return
     */
    public URL getQuestionURL(){
    	return getQuestionURL(LangMessages.getLanguage(questionLanguages.keySet()));
    }

    /**
     * Returns the link to feedback page for the specified language
     *
     * @param language  The Language for which we want the link
     *                  to the feedback page
     *
     * @return          Returns an URL to the feedback page in the
     *                  specified language, or null in case there is
     *                  no feedback page for the given language.
     */
    public URL getFeedbackURL(Language language) {
        return getURL(language, Question.FEEDBACK_INDEX);
    }
    
    public URL getFeedbackURL() {
    	return getFeedbackURL(LangMessages.getLanguage(questionLanguages.keySet()));
    }

    /**
     * @param questionSet
     * @return  Returns the difficulty for this question within the given questionSet
     */
    public Difficulties getDifficulty(Set questionSet) {
        return Set_Question.getSet_Question(questionSet, this).difficulty;
    }

    /**
     * Checks if the given answer is the correct answer for this question
     * @param answer
     * @return
     */
    public boolean isCorrectAnswer(String givenAnswer) {
        if (answerChecker == null)
            answerChecker = AnswerChecker.getAnswerChecker(answerType);
        return answerChecker.isCorrectAnswer(this.answer, givenAnswer);
    }
	@Override
	public int compareTo(Question o) {
		return getTitle().compareToIgnoreCase(o.getTitle());
	}


    /*@Override
    public String toString(){
        //return "Question: "+id+", link: "+link+", author: "+author+", correctAnswer: "+correctAnswer;
        return "Question: " + id + "author:" + author;
    }*/

	public String getQuestionFileName(Language l) {
		Question_Language ql = questionLanguages.get(l);

        if (ql == null)
            return null;
        return ql.questionFile;
        
	}
	
	public String getFeedbackFileName(Language l) {
		Question_Language ql = questionLanguages.get(l);

        if (ql == null)
            return null;
        return ql.feedbackFile;
	}
	
}
