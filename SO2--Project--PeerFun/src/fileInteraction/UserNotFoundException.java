package fileInteraction;

/**
 * @author NVH
 * @filename UserNotFoundException.java
 */
public class UserNotFoundException extends NullPointerException {

    /**
     * Make a new NullPointerException with adjusted message.
     * @param userName	    The user that could not be found.
     */
    public UserNotFoundException(String userName) {
	super("The User \'"+userName+"\' could not be found");
    }
}
