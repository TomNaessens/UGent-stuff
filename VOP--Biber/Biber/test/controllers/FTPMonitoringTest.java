package controllers;

import com.avaje.ebean.Ebean;
import models.Person;
import models.Teacher;
import org.junit.Test;
import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import play.libs.Yaml;
import play.test.Helpers;
import play.test.TestBrowser;
import play.test.WithApplication;
import utils.Hash;

import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import static org.fest.assertions.Assertions.assertThat;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static play.test.Helpers.*;

public class FTPMonitoringTest extends WithApplication {

    public void config() {
        if (Teacher.find.findRowCount() == 0) {
            Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml
                .load("test-data.yml");

            Ebean.save(all.get("fileservers"));

            Ebean.save(all.get("questions"));

            // Load persons from test-data file
            List<Person> persons = (List<Person>) (Object) all.get("persons");
            for (Person p : persons) {
                p.firstPassword = "";
                p.password = Hash.createPassword("secret");
                Ebean.save(p);
            }
        }
    }

    @Test
    public void removeServerWithQuestions() {
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
            new play.libs.F.Callback<TestBrowser>() {
                public void invoke(TestBrowser browser) {
                    config();
                    WebDriver driver = browser.getDriver();
                    driver.get("http://localhost:3333/login");
                    driver.findElement(By.id("bebrasId")).clear();
                    driver.findElement(By.id("bebrasId")).sendKeys("nkrohn");
                    driver.findElement(By.id("password")).clear();
                    driver.findElement(By.id("password")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input.btn.btn-primary")).click();
                    driver.findElement(By.linkText("Manage FTP-servers")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.xpath("//tr[@id='2']/td[7]/div/a[2]")).click();
                    assertThat(browser.pageSource().contains("There are still questions on this server. Therefore, this server cant be deleted."));
                }
            }
        );
    }

    @Test
    public void offlineServerAlert() {
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
            new play.libs.F.Callback<TestBrowser>() {
                public void invoke(TestBrowser browser) {
                    config();
                    WebDriver driver = browser.getDriver();
                    driver.get("http://localhost:3333/login");
                    driver.findElement(By.id("bebrasId")).clear();
                    driver.findElement(By.id("bebrasId")).sendKeys("nkrohn");
                    driver.findElement(By.id("password")).clear();
                    driver.findElement(By.id("password")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input.btn.btn-primary")).click();
                    assertThat(browser.pageSource().contains("One of the FTP-servers is offline"));
                }
            }
        );
    }

    @Test
    public void addServer() {
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
            new play.libs.F.Callback<TestBrowser>() {
                public void invoke(TestBrowser browser) {
                    config();
                    WebDriver driver = browser.getDriver();
                    driver.get("http://localhost:3333/login");
                    driver.findElement(By.id("bebrasId")).clear();
                    driver.findElement(By.id("bebrasId")).sendKeys("nkrohn");
                    driver.findElement(By.id("password")).clear();
                    driver.findElement(By.id("password")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input.btn.btn-primary")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.linkText("Manage FTP-servers")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.linkText("Add server")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.id("host")).clear();
                    driver.findElement(By.id("host")).sendKeys("bladibla");
                    driver.findElement(By.id("port")).clear();
                    driver.findElement(By.id("port")).sendKeys("9001");
                    driver.findElement(By.id("questionFolder")).clear();
                    driver.findElement(By.id("questionFolder")).sendKeys("questions/");
                    driver.findElement(By.id("publicLink")).clear();
                    driver.findElement(By.id("publicLink")).sendKeys("http://www.bladibla.com");
                    driver.findElement(By.id("username")).clear();
                    driver.findElement(By.id("username")).sendKeys("Biberkes");
                    driver.findElement(By.id("pass")).clear();
                    driver.findElement(By.id("pass")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input[type=\"submit\"]")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    assertThat(browser.pageSource().contains("bladibla"));
                }
            }
        );
    }

    @Test
    public void removeServerWithoutQuestions() {
        app = fakeApplication(inMemoryDatabase(), fakeGlobal());
        Helpers.running(Helpers.testServer(3333, app), Helpers.FIREFOX,
            new play.libs.F.Callback<TestBrowser>() {
                public void invoke(TestBrowser browser) {
                    config();
                    WebDriver driver = browser.getDriver();
                    driver.get("http://localhost:3333/login");
                    driver.findElement(By.id("bebrasId")).clear();
                    driver.findElement(By.id("bebrasId")).sendKeys("nkrohn");
                    driver.findElement(By.id("password")).clear();
                    driver.findElement(By.id("password")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input.btn.btn-primary")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.linkText("Manage FTP-servers")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.linkText("Add server")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    driver.findElement(By.id("host")).clear();
                    driver.findElement(By.id("host")).sendKeys("bladibla");
                    driver.findElement(By.id("port")).clear();
                    driver.findElement(By.id("port")).sendKeys("9001");
                    driver.findElement(By.id("questionFolder")).clear();
                    driver.findElement(By.id("questionFolder")).sendKeys("questions/");
                    driver.findElement(By.id("publicLink")).clear();
                    driver.findElement(By.id("publicLink")).sendKeys("http://www.bladibla.com");
                    driver.findElement(By.id("username")).clear();
                    driver.findElement(By.id("username")).sendKeys("Biberkes");
                    driver.findElement(By.id("pass")).clear();
                    driver.findElement(By.id("pass")).sendKeys("secret");
                    driver.findElement(By.cssSelector("input[type=\"submit\"]")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    assertThat(browser.pageSource().contains("bladibla"));
                    driver.findElement(By.xpath("//tr[@id='3']/td[7]/div/a[2]/i")).click();
                    driver.manage().timeouts().implicitlyWait(1500, TimeUnit.MILLISECONDS);
                    assertFalse(browser.pageSource().contains("bladibla"));
                }
            }
        );
    }

}