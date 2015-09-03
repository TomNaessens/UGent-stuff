package fileInteraction;

/**
 * @author NVH
 * @filename UserExistsException.java
 */
public class UserExistsException extends Exception {

    public UserExistsException() {
	super("The specified User already exists");
    }
}
