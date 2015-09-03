package models;


import com.avaje.ebean.Ebean;
import org.fest.assertions.Assertions;
import org.junit.Before;
import org.junit.Test;
import play.libs.Yaml;
import utils.Hash;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.List;
import java.util.Map;

import static org.fest.assertions.Assertions.assertThat;
import static play.test.Helpers.*;

public class FileServerTest {

    @Before
    public void setUp() {
        start(fakeApplication(inMemoryDatabase(), fakeGlobal()));
        Map<String, List<Object>> all = (Map<String, List<Object>>) Yaml.load("test-data.yml");
        Ebean.save(all.get("fileservers"));
    }

    @Test
    public void toStringTest() {

        FileServer f = null;

        try {
            f = new FileServer("localhost", 21, "questions/", new URL("http://www.google.com"), "tnaessens", "secret");
        } catch (MalformedURLException e) {
            assertThat(false == true);
        }

        String toString = f.toString();

        assertThat("ftp://tnaessens:secret@localhost:21/questions/".equals(toString));

    }

    @Test
    public void getAFileServerTest() {
        FileServer f = FileServer.getAFileServer();

        assertThat(f != null && f instanceof FileServer);
    }

    @Test
    public void addServer() {
        FileServer f = null;

        try {
            f = FileServer.addServer("localhost", 21, "questions/", new URL("http://www.google.com"), "tnaessens", "secret");
        } catch (MalformedURLException e) {
            assertThat(false == true);
        }

        assertThat(f != null && f instanceof FileServer);

    }


}
