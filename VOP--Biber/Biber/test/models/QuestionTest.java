package models;

import org.junit.Before;
import org.junit.Test;
import play.test.WithApplication;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;
import static org.junit.Assert.*;

    /**
     * TESTS OF CLASS QUESTION
     *
     * Methods tested:
     *  constructor
     *  getAllQuestions()
     *  getQuestion()
     *  getURLs()
     *  getQuestionURL()
     *  getFeedbackURL()
     *  isCorrectAnswer()
     *  getTitle()
     *
     */
public class QuestionTest extends WithApplication {
    @Before
    public void setUp() throws MalformedURLException {
        start(fakeApplication(inMemoryDatabase(),fakeGlobal()));

        // Add file servers
        FileServer server1 = new FileServer("ftp.host1.com", 1, "questions/", new URL("http://www.host1.com/questions/"), "ftp_user1", "secret");
        FileServer server2 = new FileServer("ftp.host2.net", 2, "questions/", new URL("ftp://public.host2.net/bebras/questions/"), "ftp_user2", "secret");

        server1.save();
        server2.save();
    }

    @Test
    public void testQuestion1() {
        // Get the server
        FileServer server = FileServer.find.byId(1l);

        // Setup question 1
        Map<Language, Question_Language> qls = new TreeMap<Language, Question_Language>();
        qls.put( Language.GERMAN,
                new Question_Language("biber am fluss", "question_de.html", "feedback_de.html", Language.GERMAN) );
        qls.put( Language.DUTCH,
                new Question_Language("bever aan de dam", "vraag.html", "antwoord.html", Language.DUTCH) );
        qls.put( Language.FRENCH,
                new Question_Language("castor à rivière", "question_fr.html", "feedback_fr.html", Language.FRENCH));

        Question question = new Question("eebral", AnswerType.MULTIPLE_CHOICE, "A", server, qls);
        question.save();

        // Test properties
        assertTrue(question.author.equals("eebral"));
        assertEquals(question.answerType, AnswerType.MULTIPLE_CHOICE);
        assertTrue(question.answer.equals("A"));
        assertEquals(question.server, server);
        assertEquals(qls.size(), question.questionLanguages.size());

        // Test methods
        assertTrue(question.getTitle(Language.DUTCH).equals("bever aan de dam"));
        assertTrue(question.getTitle(Language.FRENCH).equals("castor à rivière"));
        assertNull(question.getTitle(Language.ENGLISH));

        //assertTrue(question.getQuestionURL(Language.GERMAN).toString().equals("http://www.host1.com/questions/1/question_de.html"));
        //assertTrue(question.getFeedbackURL(Language.DUTCH).toString().equals("http://www.host1.com/questions/1/antwoord.html"));
        //assertTrue(question.getURLs(Language.FRENCH)[Question.FEEDBACK_INDEX].toString().equals("http://www.host1.com/questions/1/feedback_fr.html"));

        assertNull(question.getQuestionURL(Language.ENGLISH));
        assertNull(question.getFeedbackURL(Language.ENGLISH));
        assertNull(question.getURLs(Language.ENGLISH));
        assertNotNull(question.getURLs(Language.DUTCH));
    }

    @Test
    public void testQuestion2() {
        // Get the server
        FileServer server = FileServer.find.byId(2l);

        // Setup question 2
        Map<Language, Question_Language> qls = new TreeMap<Language, Question_Language>();
        qls.put( Language.GERMAN, new Question_Language(
                    "alle bits sind gleich", "bits_gleich.html", "bits_gleich_feedback.html",
                    Language.GERMAN)
        );

        qls.put( Language.DUTCH,
                new Question_Language("alle bits zijn gelijk", "vraag.html", "antwoord.html", Language.DUTCH) );

        Question question = new Question("François D'éclair", AnswerType.REGULAR_EXPRESSION, "^0111001$", server, qls);
        question.save();

        // Test properties
        assertTrue(question.getTitle(Language.DUTCH).equals("alle bits zijn gelijk"));
        assertNull(question.getTitle(Language.FRENCH));

        assertTrue(question.author.equals("François D'éclair"));
        assertEquals(question.answerType, AnswerType.REGULAR_EXPRESSION);
        assertTrue(question.answer.equals("^0111001$"));
        assertEquals(question.server, server);
        assertEquals(qls.size(), question.questionLanguages.size());

        // Test methods
        //assertTrue(question.getQuestionURL(Language.GERMAN).toString().equals("ftp://public.host2.net/bebras/questions/1/bits_gleich.html"));
        //assertTrue(question.getFeedbackURL(Language.DUTCH).toString().equals("ftp://public.host2.net/bebras/questions/1/antwoord.html"));

        assertNull(question.getURLs(Language.FRENCH));
        assertNull(question.getQuestionURL(Language.FRENCH));
        assertNull(question.getFeedbackURL(Language.ENGLISH));
        assertNull(question.getURLs(Language.ENGLISH));
        assertNotNull(question.getURLs(Language.DUTCH));
    }

    @Test
    public void testCorrectAnswerMultipleChoice() {
        Question question = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", null, null);

        assertTrue(question.isCorrectAnswer("A"));
        assertFalse(question.isCorrectAnswer("B"));
    }

    @Test
    public void testCorrectAnswerRegularExpression() {
        Question question = new Question("ebral", AnswerType.REGULAR_EXPRESSION, "^[0-9]*Te+[st]?ing$", null, null);

        assertTrue(question.isCorrectAnswer("Teeing"));
        assertTrue(question.isCorrectAnswer("332Tesing"));
        assertFalse(question.isCorrectAnswer("333Tsing"));
        assertFalse(question.isCorrectAnswer("22Teting "));
    }

    @Test
    public void testQuestion3(){
        Question question = new Question("test", AnswerType.MULTIPLE_CHOICE, "B", null, null);
        assertNotNull(Question.getQuestion(question.id));
        assertTrue(Question.getAllQuestions().size()>0);
    }
}
