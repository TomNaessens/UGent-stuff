package controllers;

import static play.test.Helpers.fakeApplication;
import static play.test.Helpers.fakeGlobal;
import static play.test.Helpers.inMemoryDatabase;

import java.io.File;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import models.Person;
import models.Teacher;

import org.junit.Test;
import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.WebElement;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;

import play.libs.Yaml;
import play.test.Helpers;
import play.test.TestBrowser;
import play.test.WithApplication;
import utils.Hash;

import com.avaje.ebean.Ebean;

public class RegisterPupilsByFileTest extends WithApplication {

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

    @Test
    public void uploadXLSTest() {
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
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
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.linkText("Register pupils")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        WebElement upload = driver.findElement(By.id("fileupload"));
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        upload.sendKeys(new File("Voorbeeld-data/testXLS.xls").getAbsolutePath());
                         WebDriverWait wait = new WebDriverWait(driver, 30);
                         wait.until(ExpectedConditions.visibilityOf(driver.findElement(By.id("success"))));
                    }
                });
    }

    @Test
    public void uploadXLSXTest(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
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
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.linkText("Register pupils")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        WebElement upload = driver.findElement(By.id("fileupload"));
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        upload.sendKeys(new File("Voorbeeld-data/testXLSX.xlsx").getAbsolutePath());
                         WebDriverWait wait = new WebDriverWait(driver, 30);
                         wait.until(ExpectedConditions.visibilityOf(driver.findElement(By.id("success"))));
                    }
                });
    }

    @Test
    public void uploadCSVTest(){
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
                new play.libs.F.Callback<TestBrowser>() {
                    public void invoke(TestBrowser browser) {
                        config();
                        WebDriver driver = browser.getDriver();
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
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        driver.findElement(By.linkText("Register pupils")).click();
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        WebElement upload = driver.findElement(By.id("fileupload"));
                        driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                        upload.sendKeys(new File("Voorbeeld-data/testCSV.csv").getAbsolutePath());
                         WebDriverWait wait = new WebDriverWait(driver, 30);
                         wait.until(ExpectedConditions.visibilityOf(driver.findElement(By.id("success"))));
                    }
                });
    }

}
