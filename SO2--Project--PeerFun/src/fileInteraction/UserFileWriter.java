package fileInteraction;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.EOFException;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import userManagement.User;

/**
 * @author NVH 
 * @filename UserFileWriter.java
 */
public class UserFileWriter {

    /**
     * Add a new user to the userFile if the user doesn't yet exist.
     * @param user			The user to be added.
     * @throws UserExistsException	When the user already exists.  
     */
    public void addNewUser(User user) throws UserExistsException {
	ArrayList<User> users = getUserList();	    // Get the list of users from the userFile
	if (users != null) {			    // Check if the list was found
	    for (User current : users) {	    // Check whether the user already exists
		if (user.equals(current)) {
		    throw new UserExistsException();// The user already exists
		}
	    }
	} else {				    // The list wasn't found
	    users = new ArrayList<User>();	    // Create a new list of users
	}
	users.add(user);			    // Add the user to the list
	writeToFile(users);			    // Write the list to the userFile
    }

    /**
     * Remove a user from the userFile. 
     * If the user was not found, nothing will be done.
     * @param userName			The userName of the user to be deleted.
     * @throws UserNotFoundException	When the user was not found.
     */
    public void deleteUser(String userName) throws UserNotFoundException {
	ArrayList<User> users = getUserList();		    // Get the list of users from the userFile
	if (users != null) {				    // Check if the list was found
	    for (User current : users) {		    // Search the user in the list
		if (current.getName().equals(userName)) {   // If the user is found 
		    users.remove(current);		    // Remove the user from the list
		    writeToFile(users);			    // Overwrite the userFile
		    return;				    // Only one user can be found with username 'userName'
		}					    // The user was not found in the list
	    }
	}						    // The list of users was not found
	throw new UserNotFoundException(userName);	    // Report that the user was not found
    }
    
    /**
     * Adjust the a user specified by the name in 'user'.
     * @param user			The user to be adjusted with adjusted userdata.
     * @throws UserNotFoundException	When the user was not found.
     */
    public void adjustUser(User user) throws UserNotFoundException {
	ArrayList<User> users = getUserList();		    // Get the list of users from the userFile
	if (users != null) {				    // Check if the list was found
	    for (User current : users) {		    // Search the user in the list
		if (user.equals(current)) {		    // If the user is found 
		    users.remove(current);		    // Remove the old userdata from the list
		    users.add(user);			    // Add the new userdata to the list
		    writeToFile(users);			    // Overwrite the userFile
		    return;				    // Only one user can be found with username 'userName'
		}					    // The user was not found in the list
	    }
	}						    // The list of users was not found
	throw new UserNotFoundException(user.getName());    // Report that the user was not found
    }

    /**
     * Get the list of users from the userFile.
     * @return	    The list of users from the userFile, if it was found.
     *		    Null if the list could not be found in the file.
     */
    private ArrayList<User> getUserList() {
	ArrayList<User> users = null;					// Initialise list with null value
	if (UserFileReader.userFile.exists()) {				// Check whether the userFile exists
	    try {
		ObjectInputStream in = new ObjectInputStream(		// Open inputstream from the userFile
			new BufferedInputStream(
			new FileInputStream(UserFileReader.userFile)));
		try {
		    users = (ArrayList<User>) in.readObject();		// Read the list from the userFile
		} catch (ClassNotFoundException ex) {			// The file doesn't contain a list, leave users at null value
		} finally {						// Allways close the inputstream
		    in.close();
		}
	    } catch (EOFException eofex) {				// The file is empty
		System.out.println("EOFException caught");
	    } catch (IOException ioex) {				// The file was not accessable
		System.out.println("IOException caught");
	    }
	}
	return users;							// Return list or null
    }

    /**
     * Write a list of users to the userFile. 
     * Does nothing when the userFile couldn't be accessed.
     * @param users	The list to be written to the file.
     */
    private void writeToFile(ArrayList<User> users) {
	try {
	    ObjectOutputStream out = new ObjectOutputStream(		// Open outputstream to the userFile
		    new BufferedOutputStream(
		    new FileOutputStream(UserFileReader.userFile)));
	    try{
		out.writeObject(users);					// Write the list of users to the userFile
	    }finally {							// Allways close the outputstream
		out.close();
	    }
	} catch (IOException ioex) {					// The file was not accessable
	    System.out.println("IOException caught");
	}
    }
}