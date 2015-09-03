package controllers;

import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import models.Person;
import models.Teacher;

import org.junit.Test;
import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.support.ui.ExpectedCondition;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;

import play.libs.Yaml;
import play.test.Helpers;
import play.test.TestBrowser;
import play.test.WithApplication;
import utils.Hash;

import com.avaje.ebean.Ebean;

public class AddClassTest extends WithApplication {

    @Test
    public void addClassAjax(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
                        login(driver);
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        addClass(driver, "5a");
                         ExpectedCondition<Boolean> e = new  ExpectedCondition<Boolean>() {
                         public Boolean apply(WebDriver d) {
                             return models.Class.findTeacherClasses("hswimberghe").size() == 2;
                         }
                         };
                        WebDriverWait wait = new WebDriverWait(driver, 6);
                        wait.until(e);
                    }
                });

    }

    @Test
    public void addDoubleClass(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
                        login(driver);
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        addClass(driver, "5a");
                         ExpectedCondition<Boolean> e = new  ExpectedCondition<Boolean>() {
                         public Boolean apply(WebDriver d) {
                             return models.Class.findTeacherClasses("hswimberghe").size() == 2;
                         }
                         };
                        WebDriverWait wait = new WebDriverWait(driver, 10);
                        wait.until(e);
                        addClass(driver, "5a");
                        wait.until(ExpectedConditions.visibilityOf(driver.findElement(By.className("exists"))));
                    }
                });
    }

    @Test
    public void addEmptyClass(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
                        login(driver);
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        addClass(driver, "");
                        WebDriverWait wait = new WebDriverWait(driver, 6);
                        wait.until(ExpectedConditions.visibilityOf(driver.findElement(By.className("empty"))));
                    }
                });
    }

    public void addClass(WebDriver driver, String name){
        driver.findElement(By.id("popover")).click();
        driver.findElement(By.id("className")).click();
        driver.findElement(By.id("className")).clear();
        driver.findElement(By.id("className")).sendKeys(name);
        driver.findElement(By.cssSelector("button.btn.btn-primary")).click();
    }

    public void login(WebDriver driver){
        driver.get("http://localhost:3333/login");
        driver.findElement(By.id("bebrasId")).clear();
        driver.findElement(By.id("bebrasId")).sendKeys(
                "hswimberghe");
        driver.findElement(By.id("password")).clear();
        driver.findElement(By.id("password"))
                .sendKeys("secret");
        driver.findElement(
                By.cssSelector("input.btn.btn-primary"))
                .click();
    }

    public void config() {
        if (Teacher.find.findRowCount() == 0) {
            Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml
                    .load("test-data.yml");

            // Save Competitions
            Ebean.save(all.get("competitions"));
            // Load schools
            Ebean.save(all.get("schools"));

            // Load persons from test-data file
            List<Person> persons = (List<Person>) (Object) all.get("persons");
            for (Person p : persons) {
                p.firstPassword = "";
                p.password = Hash.createPassword("secret");
                Ebean.save(p);
                if (p instanceof Teacher)
                    Ebean.saveManyToManyAssociations(p, "schools");
            }
            // For other data, see up
            Ebean.save(all.get("classes"));
        }
    }

}
