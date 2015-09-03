package controllers;

import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

import static org.junit.Assert.assertTrue;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import org.junit.Test;
import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;

import models.Person;
import models.Teacher;

import com.avaje.ebean.Ebean;

import play.libs.Yaml;
import play.test.Helpers;
import play.test.TestBrowser;
import play.test.WithApplication;
import utils.Hash;

public class AddSchoolToTeacherTest extends WithApplication{
    
    
    @Test
    public void addSchoolToTeacher(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        int initialSize = Teacher.getTeacher("hswimberghe").schools.size();
                        WebDriver driver = browser.getDriver();
                        login(driver);
                        driver.get("http://localhost:3333" + "/profile");
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.linkText("OLVA")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        WebDriverWait wait = new WebDriverWait(driver, 6);
                        wait.until(ExpectedConditions.presenceOfElementLocated(By.className("teacher")));
                        driver.findElement(By.linkText("Hannes Swimberghe")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.id("popover")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.name("school")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.cssSelector("button.btn.btn-primary")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        assertTrue(Teacher.getTeacher("hswimberghe").schools.size() == initialSize+1);
                    }
                });
    }
    
    @Test
    public void checkOrganizerProfilePage(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
                        login(driver);
                        driver.get("http://localhost:3333" + "/profile");
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        assertTrue(driver.findElements(By.className("collapse")).size()==3);
                    }
                });
        
        
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
    
    
    public void login(WebDriver driver){
        driver.get("http://localhost:3333/login");
        driver.findElement(By.id("bebrasId")).clear();
        driver.findElement(By.id("bebrasId")).sendKeys(
                "ebral");
        driver.findElement(By.id("password")).clear();
        driver.findElement(By.id("password"))
                .sendKeys("secret");
        driver.findElement(
                By.cssSelector("input.btn.btn-primary"))
                .click();
    }
    

}
