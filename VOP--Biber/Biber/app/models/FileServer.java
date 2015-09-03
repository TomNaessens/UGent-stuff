package models;

import org.apache.commons.net.ftp.FTPClient;
import play.data.validation.Constraints.Required;
import play.db.ebean.Model;
import utils.Obfuscate;

import javax.persistence.Entity;
import javax.persistence.Id;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Random;

@Entity
public class FileServer extends Model {
    @Id
    public Long id;

    // The hostname of the ftp server (e.g. ftp.server1.com)
    @Required
    public String host;
    // The port of the ftp server (e.g. 12345)
    @Required
    public int port;

    // The folder in the ftp server to the questions
    public String questionFolder;

    // The base url to the questions on the public html server (e.g. http://www.server1.com/questions)
    @Required
    public URL publicLink;

    // Login information for the ftp server
    @Required
    public String username;
    @Required
    public String pass;

    public static Finder<Long, FileServer> find = new Finder(Long.class, FileServer.class);

    public FileServer(String host, int port, String questionFolder, URL publicLink, String username, String pass) {
        this.host = host;
        this.port = port;
        this.questionFolder = questionFolder;
        this.publicLink = publicLink;
        this.username = username;
        this.pass = Obfuscate.obfuscate(pass);
    }

    public static List<FileServer> all() {
        return find.all();
    }

    public static FileServer addServer(String host, int port, String questionFolder, URL publicLink, String username, String pass) {
        FileServer f = new FileServer(host, port, questionFolder, publicLink, username, pass);
        f.save();
        return f;
    }

    /**
     * returns a random file server
     * @return
     */
    public static FileServer getAFileServer() {
        List<FileServer> list = find.all();
        Random rand = new Random();
        return list.get(rand.nextInt(list.size()));
    }

    public String toString() {
        return "ftp://" + username + ":" + Obfuscate.deObfuscate(pass) + "@" + host + ":" + port + "/" + questionFolder;
    }

    public boolean uploadFile(File file, Question q, String name) {
    	boolean succes = false;
    	try {
    		FTPClient client = new FTPClient();
			client.connect(host);
			client.login(username, Obfuscate.deObfuscate(pass));
			client.cwd(questionFolder);
			//TODO: hash the directory to deny random access
			client.mkd("" + q.id);
			client.cwd("" + q.id);
			client.setFileType(FTPClient.BINARY_FILE_TYPE);
			if(file.isDirectory()) {
				succes = uploadDirectory(file, client);
			} else {
				succes = uploadFile(file, name, client);
			}
			client.logout();
            client.disconnect();
		} catch (IOException e) {
            System.err.println(e);
            System.err.println(file.getName());
            System.err.println("error");
            succes = false;
		} 
    	return succes;
    }
    
    
    private boolean uploadDirectory(File file,FTPClient client) throws IOException {
    	if(!file.isDirectory()) {
    		// shouldn't happen
    		return false;
    	} else {
    		client.mkd(""+file.getName());
    		client.cwd(""+file.getName());
    		File[] files = file.listFiles();
    		for(File f : files) {
    			if(f.isDirectory()) {
    				uploadDirectory(f, client);
    			} else {
    				if(!uploadFile(f,f.getName(),client)) {
    					return false;
    				}
    			}
    		}
    		
    		client.cwd("..");
    		return true;
    	}
    }
    
    private boolean uploadFile(File file, String name, FTPClient client) throws IOException {
    	boolean succes = false;
		FileInputStream inputStream = new FileInputStream(file);
		succes = client.storeFile(name, inputStream );
		inputStream.close();
		return succes;
    }
}
