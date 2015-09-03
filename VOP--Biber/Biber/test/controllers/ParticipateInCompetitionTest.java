package controllers;

import com.avaje.ebean.Ebean;
import models.*;
import models.Class;
import org.fluentlenium.adapter.FluentTest;
import org.fluentlenium.core.domain.FluentList;
import org.fluentlenium.core.domain.FluentWebElement;
import org.junit.Test;
import org.openqa.selenium.By;
import play.libs.Yaml;
import play.test.FakeApplication;
import play.test.Helpers;
import play.test.TestBrowser;
import utils.Hash;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.TimeUnit;

import static org.fluentlenium.core.filter.FilterConstructor.*;
import static org.junit.Assert.*;
import static play.test.Helpers.*;

public class ParticipateInCompetitionTest extends FluentTest {

    private static FakeApplication app;

    public void loadData() {
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        List<Person> persons = (List<Person>) (Object) all.get("persons");
        // Because yaml doesn't uses default empty constructor
        for (Person person : persons) {
            person.password = Hash.createPassword("secret");
            // This is logintest, so assume that account is already activated by
            // setting firstpassword to empty string
            person.firstPassword = "";
            Ebean.save(person);
            if (person instanceof Teacher)
                Ebean.saveManyToManyAssociations(person, "schools");
        }
        Ebean.save(all.get("classes"));
        Ebean.save(all.get("schools"));
    }

    /**
     * Participate in an unrestricted quiz as an anonymous user
     */
    @Test
    public void participateInAnonymousUnrestrictedQuiz() {
        // We should be able to access this as an anonymous user
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
            new play.libs.F.Callback<TestBrowser>() {
                @Override
                public void invoke(TestBrowser browser) throws MalformedURLException {
                    browser.manage().timeouts().implicitlyWait(2, TimeUnit.SECONDS);

                    // Create an unrestricted competition
                    Set_Language sl = new Set_Language("Unrestricted question set", Language.ENGLISH);
                    Set questionSet = new Set(1000, false, Level.EWOK.name(), CompetitionType.UNRESTRICTED, sl);
                    questionSet.save();

                    FileServer fs = new FileServer("localhost", 22, "questions", new URL("http://localhost/questions/"),
                            "user", "pass");
                    fs.save();

                    Map<Language, Question_Language> qlMap = new TreeMap<Language, Question_Language>();
                    qlMap.put(Language.ENGLISH,
                            new Question_Language("Question 1", "question.html", "feedback.html", Language.ENGLISH)
                    );
                    Question question1 = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", fs, qlMap);
                    question1.save();
                    Set_Question sq1 = new Set_Question(Difficulties.AVERAGE, (short) 10, (short) 12, question1, questionSet);
                    sq1.save();

                    qlMap = new TreeMap<Language, Question_Language>();
                    qlMap.put(Language.ENGLISH,
                            new Question_Language("Question 2", "question.html", "feedback.html", Language.ENGLISH)
                    );
                    Question question2 = new Question("ebral", AnswerType.REGULAR_EXPRESSION, "^abcdef$", fs, qlMap);
                    question2.save();
                    Set_Question sq2 = new Set_Question(Difficulties.HARD, (short) 20, (short) 14, question2, questionSet);
                    sq2.save();

                    Competition competition = Competition.createUnrestrictedCompetition(questionSet);
                    competition.save();

                    // STEP 0
                    // Select a language and go to unrestricted competitions page
                    browser.goTo("localhost:3333/?lang=" + Language.ENGLISH.name());
                    browser.manage().timeouts().implicitlyWait(2, TimeUnit.SECONDS);
                    browser.goTo("localhost:3333/urq");
                    browser.manage().timeouts().implicitlyWait(2, TimeUnit.SECONDS);
                    // STEP 1
                    // Competition should not be visible
                    assertEquals(0, browser.find("a", withText().contains("Unrestricted question set")).size());

                    // STEP 2
                    // Make the competition visible
                    Competition.toggleUnrestrictedCompetition(questionSet);
                    competition.save();

                    // Reload the page and check if visible
                    browser.goTo("localhost:3333/urq");
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                    FluentList<FluentWebElement> fl = browser.find("a", withText().contains("Unrestricted question set"));
                    assertEquals(1, fl.size());

                    // STEP 3
                    // Go to the start page of the competition and check if it displays the properties correctly
                    fl.first().click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    FluentWebElement f = browser.findFirst("li", withText().contains("level"));
                    assertTrue(f.getText().contains(Level.EWOK.toString()));
                    f = browser.findFirst("li", withText().contains("Number of questions"));
                    assertTrue(f.getText().contains(new Integer(questionSet.size()).toString()));

                    // STEP 4
                    // Start the competition
                    browser.findFirst("input").click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // Does it display the questions correctly?
                    FluentWebElement el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                    FluentWebElement el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                    // Questions not yet answered?
                    assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));
                    assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                    // Current question is question 1?
                    assertEquals("Question 1", browser.findFirst("#content h1").getText());
                    assertTrue(el1.html().contains("<b>"));
                    assertFalse(el2.html().contains("<b>"));

                    // Level displayed correctly?
                    assertEquals(Difficulties.AVERAGE.toString(), browser.findFirst(".difficulty").getText());

                    // STEP 5
                    // Enter an (incorrect) answer to question1
                    browser.findFirst("button", withText("C")).click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // STEP 6
                    // Does it display the questions correctly?
                    el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                    el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                    // Only first question answered?
                    assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                    assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                    // Current question is question 2?
                    assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                    assertFalse(el1.html().contains("<b>"));
                    assertTrue(el2.html().contains("<b>"));

                    // Level displayed correctly?
                    assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                    // STEP 7
                    // Enter an (incorrect) answer to question2
                    browser.fill("textarea").with("abcdeZ");
                    browser.findFirst("input[type=submit]").click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // Does it display the questions correctly?
                    el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                    el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                    // Both questions answered?
                    assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                    assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));

                    // Current question is question 2?
                    assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                    assertFalse(el1.html().contains("<b>"));
                    assertTrue(el2.html().contains("<b>"));

                    // Level displayed correctly?
                    assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                    // Is the given answer filled in?
                    assertEquals("abcdeZ", browser.findFirst("textarea").getText());

                    // STEP 9
                    // Change the answer to question 2
                    browser.fill("textarea").with("test");
                    browser.findFirst("input[type=submit]").click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // did it update the answer?
                    assertEquals("test", browser.findFirst("textarea").getText());

                    // STEP 10
                    // Go back to question 1
                    browser.findFirst("a", withText("Question 1")).click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // Current question is question 1?
                    el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                    el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                    assertTrue(browser.findFirst("#content h1").getText().equals("Question 1"));
                    assertTrue(el1.html().contains("<b>"));
                    assertFalse(el2.html().contains("<b>"));

                    // Is the given answer selected?
                    assertFalse(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                    assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                    assertTrue(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                    assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                    // STEP 11
                    // Change the answer to question 1
                    browser.findFirst("button", withText("A")).click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // Go back to question 1
                    browser.findFirst("a", withText("Question 1")).click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                    // Check if the new answer is selected
                    assertTrue(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                    assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                    assertFalse(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                    assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                    // STEP 12
                    // Finish the competition
                    browser.findFirst("a", with("href").equalTo("#finishDialog")).click();
                    browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                    browser.findFirst("input", withId("submitFinish")).submit();

                    // STEP 13
                    // Points and given answers shown correctly?
                    assertTrue(browser.findFirst("tr", withText().contains("Initial Number of Points")).getText()
                            .contains(new Integer(questionSet.getInitialPoints()).toString()));

                    // Question 1
                    el1 = browser.findFirst("tr", withText().contains("Question 1"));
                    fl = el1.find("td");

                    FluentWebElement el = fl.get(1).findFirst("span");
                    assertEquals("A", el.getText());
                    assertTrue(el.getAttribute("style").contains("green"));

                    el = fl.get(2).findFirst("a");
                    assertEquals(question1.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                    el = fl.get(3).findFirst("span");
                    assertEquals(new Short(Set_Question.getSet_Question(questionSet, question1).correctPoints).toString(),
                            el.getText());

                    // Question 2
                    el1 = browser.findFirst("tr", withText().contains("Question 2"));
                    fl = el1.find("td");

                    el = fl.get(1).findFirst("span");
                    assertEquals("test", el.getText());
                    assertTrue(el.getAttribute("style").contains("red"));

                    el = fl.get(2).findFirst("a");
                    assertEquals(question2.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                    el = fl.get(3).findFirst("span");
                    assertEquals(new Short(Set_Question.getSet_Question(questionSet, question2).incorrectPoints).toString(),
                            el.getText());
                }
            }
        );
    }

    /**
     * Participate in an unrestricted quiz as a logged in user
     */
    @Test
    public void participateInLoggedInUnrestrictedQuiz() {
        // We should be able to access this as an anonymous user
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    @Override
                    public void invoke(TestBrowser browser) throws MalformedURLException {
                        loadData();

                        browser.manage().timeouts().implicitlyWait(3, TimeUnit.SECONDS);

                        // Create an unrestricted competition
                        Set_Language sl = new Set_Language("Unrestricted question set", Language.ENGLISH);
                        Set questionSet = new Set(1000, false, Level.EWOK.name(), CompetitionType.UNRESTRICTED, sl);
                        questionSet.save();

                        FileServer fs = new FileServer("localhost", 22, "questions", new URL("http://localhost/questions/"),
                                "user", "pass");
                        fs.save();

                        Map<Language, Question_Language> qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 1", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question1 = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", fs, qlMap);
                        question1.save();
                        Set_Question sq1 = new Set_Question(Difficulties.AVERAGE, (short) 10, (short) 12, question1, questionSet);
                        sq1.save();

                        qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 2", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question2 = new Question("ebral", AnswerType.REGULAR_EXPRESSION, "^abcdef$", fs, qlMap);
                        question2.save();
                        Set_Question sq2 = new Set_Question(Difficulties.HARD, (short) 20, (short) 14, question2, questionSet);
                        sq2.save();

                        Competition competition = Competition.createUnrestrictedCompetition(questionSet);
                        competition.save();

                        // STEP 0
                        // Select a language, log in and go to unrestricted competitions page
                        browser.goTo("localhost:3333/?lang=" + Language.ENGLISH.name());
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.click("a", withText().contains("Login"));
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.fill("#bebrasId").with("tvanregenmortel");
                        browser.fill("#password").with("secret");
                        browser.click("input[type=submit]");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        browser.goTo("localhost:3333/urq");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 1
                        // Competition should not be visible
                        assertEquals(0, browser.find("a", withText().contains("Unrestricted question set")).size());

                        // STEP 2
                        // Make the competition visible
                        Competition.toggleUnrestrictedCompetition(questionSet);
                        competition.save();

                        // Reload the page and check if visible
                        browser.goTo("localhost:3333/urq");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        FluentList<FluentWebElement> fl = browser.find("a", withText().contains("Unrestricted question set"));
                        assertEquals(1, fl.size());

                        // STEP 3
                        // Go to the start page of the competition and check if it displays the properties correctly
                        fl.first().click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        FluentWebElement f = browser.findFirst("li", withText().contains("level"));
                        assertTrue(f.getText().contains(Level.EWOK.toString()));
                        f = browser.findFirst("li", withText().contains("Number of questions"));
                        assertTrue(f.getText().contains(new Integer(questionSet.size()).toString()));

                        // STEP 4
                        // Start the competition
                        browser.findFirst("input").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        FluentWebElement el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        FluentWebElement el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Questions not yet answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 1?
                        assertEquals("Question 1", browser.findFirst("#content h1").getText());
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.AVERAGE.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 5
                        // Enter an (incorrect) answer to question1
                        browser.findFirst("button", withText("C")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 6
                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Only first question answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 7
                        // Enter an (incorrect) answer to question2
                        browser.fill("textarea").with("abcdeZ");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Both questions answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // Is the given answer filled in?
                        assertEquals("abcdeZ", browser.findFirst("textarea").getText());

                        // STEP 9
                        // Change the answer to question 2
                        browser.fill("textarea").with("test");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // did it update the answer?
                        assertEquals("test", browser.findFirst("textarea").getText());

                        // STEP 10
                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Current question is question 1?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 1"));
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Is the given answer selected?
                        assertFalse(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertTrue(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 11
                        // Change the answer to question 1
                        browser.findFirst("button", withText("A")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Check if the new answer is selected
                        assertTrue(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 12
                        // Finish the competition
                        browser.findFirst("a", with("href").equalTo("#finishDialog")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.findFirst("input", withId("submitFinish")).submit();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);


                        // STEP 13
                        // Points and given answers shown correctly?
                        assertTrue(browser.findFirst("tr", withText().contains("Initial Number of Points")).getText()
                                .contains(new Integer(questionSet.getInitialPoints()).toString()));

                        // Question 1
                        el1 = browser.findFirst("tr", withText().contains("Question 1"));
                        fl = el1.find("td");

                        FluentWebElement el = fl.get(1).findFirst("span");
                        assertEquals("A", el.getText());
                        assertTrue(el.getAttribute("style").contains("green"));

                        el = fl.get(2).findFirst("a");
                        assertEquals(question1.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                        el = fl.get(3).findFirst("span");
                        assertEquals(new Short(Set_Question.getSet_Question(questionSet, question1).correctPoints).toString(),
                                el.getText());

                        // Question 2
                        el1 = browser.findFirst("tr", withText().contains("Question 2"));
                        fl = el1.find("td");

                        el = fl.get(1).findFirst("span");
                        assertEquals("test", el.getText());
                        assertTrue(el.getAttribute("style").contains("red"));

                        el = fl.get(2).findFirst("a");
                        assertEquals(question2.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                        el = fl.get(3).findFirst("span");
                        assertEquals(new Short(Set_Question.getSet_Question(questionSet, question2).incorrectPoints).toString(),
                                el.getText());

                        // We should not be able to do this quiz again
                        browser.goTo("localhost:3333/urq");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.find("a", withText().contains("Unrestricted question set")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        assertTrue(browser.pageSource().contains("You have already taken this competition and can not take it twice"));
                    }
                }
        );
    }

    /**
     * Participate in a local quiz as a logged in user
     */
    @Test
    public void participateInLoggedInLocalQuiz() {
        // We should be able to access this as an anonymous user
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    @Override
                    public void invoke(TestBrowser browser) throws MalformedURLException {
                        loadData();

                        browser.manage().timeouts().implicitlyWait(3, TimeUnit.SECONDS);

                        // Create a local competition
                        Set_Language sl = new Set_Language("Unrestricted question set", Language.ENGLISH);
                        Set questionSet = new Set(1000, false, Level.EWOK.name(), CompetitionType.UNRESTRICTED, sl);
                        questionSet.save();

                        FileServer fs = new FileServer("localhost", 22, "questions", new URL("http://localhost/questions/"),
                                "user", "pass");
                        fs.save();

                        Map<Language, Question_Language> qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 1", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question1 = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", fs, qlMap);
                        question1.save();
                        Set_Question sq1 = new Set_Question(Difficulties.AVERAGE, (short) 10, (short) 12, question1, questionSet);
                        sq1.save();

                        qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 2", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question2 = new Question("ebral", AnswerType.REGULAR_EXPRESSION, "^abcdef$", fs, qlMap);
                        question2.save();
                        Set_Question sq2 = new Set_Question(Difficulties.HARD, (short) 20, (short) 14, question2, questionSet);
                        sq2.save();

                        Competition_Language cl = new Competition_Language("Local Competition", Language.ENGLISH);
                        Competition competition = Competition.createCompetition(cl, CompetitionType.LOCAL);
                        competition.addQuestionSets(new Set[] { questionSet });
                        competition.save();

                        Pupil pupil = Pupil.getPupil("tvanregenmortel");
                        Class clazz = pupil.currentClass;

                        Class_Competition.createClassCompetition(clazz, competition);
                        Class_Competition cc = Class_Competition.findClassCompetition(competition.id, clazz.id);

                        // STEP 0
                        // Select a language, log in
                        browser.goTo("localhost:3333/?lang=" + Language.ENGLISH.name());
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.click("a", withText().contains("Login"));
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.fill("#bebrasId").with("tvanregenmortel");
                        browser.fill("#password").with("secret");
                        browser.click("input[type=submit]");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);


                        // STEP 1
                        // Competition should not be visible
                        assertEquals(0, browser.find("a", withText().contains("Local Competition")).size());

                        // STEP 2
                        // Make the competition visible
                        clazz.openCompetition(competition);
                        competition.isOpen = Competition.VISIBLE;
                        competition.save();

                        // Reload the page and check if visible
                        browser.goTo("localhost:3333/profile");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        FluentList<FluentWebElement> fl = browser.find("a", withText().contains("Local Competition"));
                        assertEquals(1, fl.size());

                        // STEP 3
                        // Go to the start page of the competition and check if it displays the properties correctly
                        fl.first().click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        browser.manage().timeouts().implicitlyWait(5, TimeUnit.SECONDS);

                        FluentWebElement f = browser.findFirst("li", withText().contains("level"));
                        assertTrue(f.getText().contains(Level.EWOK.toString()));
                        f = browser.findFirst("li", withText().contains("Number of questions"));
                        assertTrue(f.getText().contains(new Integer(questionSet.size()).toString()));

                        // STEP 4
                        // Start the competition
                        browser.findFirst("input").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        FluentWebElement el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        FluentWebElement el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Questions not yet answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 1?
                        assertEquals("Question 1", browser.findFirst("#content h1").getText());
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.AVERAGE.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 5
                        // Enter an (incorrect) answer to question1
                        browser.findFirst("button", withText("C")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 6
                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Only first question answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 7
                        // Enter an (incorrect) answer to question2
                        browser.fill("textarea").with("abcdeZ");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Both questions answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // Is the given answer filled in?
                        assertEquals("abcdeZ", browser.findFirst("textarea").getText());

                        // STEP 9
                        // Change the answer to question 2
                        browser.fill("textarea").with("test");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // did it update the answer?
                        assertEquals("test", browser.findFirst("textarea").getText());

                        // STEP 10
                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Current question is question 1?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 1"));
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Is the given answer selected?
                        assertFalse(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertTrue(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 11
                        // Change the answer to question 1
                        browser.findFirst("button", withText("A")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Check if the new answer is selected
                        assertTrue(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 12
                        // Finish the competition
                        browser.findFirst("a", with("href").equalTo("#finishDialog")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.findFirst("input", withId("submitFinish")).submit();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 13
                        // We should not be able to do this quiz again
                        browser.goTo("localhost:3333/profile");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.find("a", withText().contains("Local Competition")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        assertTrue(browser.pageSource().contains("You have already taken this competition and can not take it twice"));

                        // STEP 14
                        // Go to history
                        browser.goTo("http://localhost:3333/profile/history");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Feedback and points shouldn't be visible until the competition is closed
                        assertFalse(browser.pageSource().contains("Local Competition"));

                        // Close the competition
                        clazz.closeCompetition(competition);
                        clazz.save();

                        // Reload the page
                        browser.goTo("http://localhost:3333/profile/history");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.findFirst("a", withText().contains("Local Competition")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Points and given answers shown correctly?
                        assertTrue(browser.findFirst("tr", withText().contains("Initial Number of Points")).getText()
                                .contains(new Integer(questionSet.getInitialPoints()).toString()));

                        // Question 1
                        el1 = browser.findFirst("tr", withText().contains("Question 1"));
                        fl = el1.find("td");

                        FluentWebElement el = fl.get(1).findFirst("span");
                        assertEquals("A", el.getText());
                        assertTrue(el.getAttribute("style").contains("green"));

                        el = fl.get(2).findFirst("a");
                        assertEquals(question1.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                        el = fl.get(3).findFirst("span");
                        assertEquals(new Short(Set_Question.getSet_Question(questionSet, question1).correctPoints).toString(),
                                el.getText());

                        // Question 2
                        el1 = browser.findFirst("tr", withText().contains("Question 2"));
                        fl = el1.find("td");

                        el = fl.get(1).findFirst("span");
                        assertEquals("test", el.getText());
                        assertTrue(el.getAttribute("style").contains("red"));

                        el = fl.get(2).findFirst("a");
                        assertEquals(question2.getFeedbackURL(Language.ENGLISH).toString(), el.getAttribute("href"));

                        el = fl.get(3).findFirst("span");
                        assertEquals(new Short(Set_Question.getSet_Question(questionSet, question2).incorrectPoints).toString(),
                                el.getText());
                    }
                }
        );
    }

    /**
     * Participate in an official quiz as a logged in user
     */
    // Fail to make competition visible because of strange ebean bug...
    //@Test
    public void participateInLoggedInOfficialQuiz() {
        // We should be able to access this as an anonymous user
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    @Override
                    public void invoke(TestBrowser browser) throws MalformedURLException {
                        loadData();

                        browser.manage().timeouts().implicitlyWait(3, TimeUnit.SECONDS);

                        // Create an official competition
                        Set_Language sl = new Set_Language("Unrestricted question set", Language.ENGLISH);
                        Set questionSet = new Set(1000, false, Level.EWOK.name(), CompetitionType.UNRESTRICTED, sl);
                        questionSet.save();

                        FileServer fs = new FileServer("localhost", 22, "questions", new URL("http://localhost/questions/"),
                                "user", "pass");
                        fs.save();

                        Map<Language, Question_Language> qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 1", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question1 = new Question("ebral", AnswerType.MULTIPLE_CHOICE, "A", fs, qlMap);
                        question1.save();
                        Set_Question sq1 = new Set_Question(Difficulties.AVERAGE, (short) 10, (short) 12, question1, questionSet);
                        sq1.save();

                        qlMap = new TreeMap<Language, Question_Language>();
                        qlMap.put(Language.ENGLISH,
                                new Question_Language("Question 2", "question.html", "feedback.html", Language.ENGLISH)
                        );
                        Question question2 = new Question("ebral", AnswerType.REGULAR_EXPRESSION, "^abcdef$", fs, qlMap);
                        question2.save();
                        Set_Question sq2 = new Set_Question(Difficulties.HARD, (short) 20, (short) 14, question2, questionSet);
                        sq2.save();

                        Competition_Language cl = new Competition_Language("Official Competition", Language.ENGLISH);
                        Competition competition = Competition.createCompetition(cl, CompetitionType.OFFICIAL);
                        competition.addQuestionSets(new Set[] { questionSet });
                        competition.save();

                        Pupil pupil = Pupil.getPupil("tvanregenmortel");
                        Class clazz = pupil.currentClass;

                        Class_Competition.createClassCompetition(clazz, competition);
                        Class_Competition cc = Class_Competition.findClassCompetition(competition.id, clazz.id);

                        // STEP 0
                        // Select a language, log in
                        browser.goTo("localhost:3333/?lang=" + Language.ENGLISH.name());
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.click("a", withText().contains("Login"));
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.fill("#bebrasId").with("tvanregenmortel");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.fill("#password").with("secret");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.click("input[type=submit]");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 1
                        // Competition should not be visible
                        assertEquals(0, browser.find("a", withText().contains("Official Competition")).size());

                        // STEP 2
                        // Make the competition visible
                        clazz.openCompetition(competition);
                        competition.isOpen = Competition.VISIBLE;
                        competition.save();

                        // isOpen is not saved correctly due to strange ebean bug :/ (this only happens during testing though)
                        assertEquals(Competition.VISIBLE, Competition.findById(competition.id).isOpen);

                        // Reload the page and check if visible
                        browser.goTo("localhost:3333/profile");
                        FluentList<FluentWebElement> fl = browser.find("a", withText().contains("Official Competition"));
                        assertEquals(1, fl.size());

                        // STEP 3
                        // Go to the start page of the competition and check if it displays the properties correctly
                        fl.first().click();
                        browser.manage().timeouts().implicitlyWait(5, TimeUnit.SECONDS);

                        FluentWebElement f = browser.findFirst("li", withText().contains("level"));
                        assertTrue(f.getText().contains(Level.EWOK.toString()));
                        f = browser.findFirst("li", withText().contains("Number of questions"));
                        assertTrue(f.getText().contains(new Integer(questionSet.size()).toString()));

                        // STEP 4
                        // Start the competition
                        browser.findFirst("input").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        FluentWebElement el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        FluentWebElement el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Questions not yet answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 1?
                        assertEquals("Question 1", browser.findFirst("#content h1").getText());
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.AVERAGE.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 5
                        // Enter an (incorrect) answer to question1
                        browser.findFirst("button", withText("C")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 6
                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Only first question answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-question-sign"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // STEP 7
                        // Enter an (incorrect) answer to question2
                        browser.fill("textarea").with("abcdeZ");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Does it display the questions correctly?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        // Both questions answered?
                        assertTrue(el1.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));
                        assertTrue(el2.getElement().findElement(By.tagName("i")).getAttribute("class").equals("icon-ok"));

                        // Current question is question 2?
                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 2"));
                        assertFalse(el1.html().contains("<b>"));
                        assertTrue(el2.html().contains("<b>"));

                        // Level displayed correctly?
                        assertEquals(Difficulties.HARD.toString(), browser.findFirst(".difficulty").getText());

                        // Is the given answer filled in?
                        assertEquals("abcdeZ", browser.findFirst("textarea").getText());

                        // STEP 9
                        // Change the answer to question 2
                        browser.fill("textarea").with("test");
                        browser.findFirst("input[type=submit]").click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // did it update the answer?
                        assertEquals("test", browser.findFirst("textarea").getText());

                        // STEP 10
                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Current question is question 1?
                        el1 = browser.findFirst(".question-list li", withText().contains("Question 1"));
                        el2 = browser.findFirst(".question-list li", withText().contains("Question 2"));

                        assertTrue(browser.findFirst("#content h1").getText().equals("Question 1"));
                        assertTrue(el1.html().contains("<b>"));
                        assertFalse(el2.html().contains("<b>"));

                        // Is the given answer selected?
                        assertFalse(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertTrue(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 11
                        // Change the answer to question 1
                        browser.findFirst("button", withText("A")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Go back to question 1
                        browser.findFirst("a", withText("Question 1")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // Check if the new answer is selected
                        assertTrue(browser.findFirst("button", withText("A")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("B")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("C")).getAttribute("style").contains("green"));
                        assertFalse(browser.findFirst("button", withText("D")).getAttribute("style").contains("green"));

                        // STEP 12
                        // Finish the competition
                        browser.findFirst("a", with("href").equalTo("#finishDialog")).click();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.findFirst("input", withId("submitFinish")).submit();
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);

                        // STEP 13
                        // We should not be able to do this quiz again
                        browser.goTo("localhost:3333/profile");
                        browser.manage().timeouts().implicitlyWait(1, TimeUnit.SECONDS);
                        browser.find("a", withText().contains("Official Competition")).click();

                        assertTrue(browser.pageSource().contains("You have already taken this competition and can not take it twice"));
                    }
                }
        );
    }

}
