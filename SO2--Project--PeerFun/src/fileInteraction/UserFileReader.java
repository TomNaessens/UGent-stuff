package fileInteraction;

import java.io.BufferedInputStream;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.ArrayList;
import userManagement.User;

/**
 * @author NVH 
 * @filename UserFileReader.java
 */
public class UserFileReader {

    public static final File fileDir = new File("PeerFunData/");
    public static final File userFile = new File(fileDir.getPath()+"/PeerFunUsers.txt");

    public UserFileReader() {
	fileDir.mkdir();
    }
    
    /**
     * Read the user with the specified userName from the userFile.
     *
     * @param userName	The name of the user to be read.
     * @return	The user with the specified userName from the userFile. Null if
     * the user wasn't found.
     */
    public User readUser(String userName) {
	User user = null;				    // Initialise user with null value
	ArrayList<User> users = getUserList();		    // Get the list of users from the userFile 
	if (users != null) {				    // Check if the list was found
	    for (User current : users) {		    // Search the user
		if (current.getName().equals(userName)) {
		    user = current;
		}
	    }
	}
	return user;					    // Return the user of null if not found
    }

    /**
     * Check whether the user with the specified userName exists.
     * @param userName	The name of the user to be checked. 
     * @return		True if the user exists.
     *			False if the user doesn't exist or it wasn't found.
     */
    public boolean userExists(String userName) {
	return readUser(userName) != null;
    }

    private ArrayList<User> getUserList() {
	ArrayList<User> users = null;
	if (userFile.exists()) {
	    try {
		ObjectInputStream in = new ObjectInputStream(
			new BufferedInputStream(
			new FileInputStream(userFile)));

		// Haal de lijst van gebruikers op
		try {
		    users = (ArrayList<User>) in.readObject();
		} catch (ClassNotFoundException ex) {
		    // Er bestaat dus geen enkele user
		    users = null;
		} finally {
		    in.close();
		}
	    } catch (EOFException ex) {
	    } catch (IOException ex) {
	    }
	}
	return users;
    }
}
