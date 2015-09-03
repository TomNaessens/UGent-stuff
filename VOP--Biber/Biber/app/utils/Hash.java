package utils;

//import org.mindrot.jbcrypt.*;

/**
 * Utility class handling the encrypting and validation of passwords
 * @author Hannes
 *
 */
public class Hash {
    
    /**
     * Create an encrypted password from a clear string.
     *
     * @param plaintext the plaintext password
     * @return an encrypted password of the clear string
     */
    public static String createPassword(String plaintext) {
        if (plaintext == null) {
            //TODO: handle this exception?
        }
        return BCrypt.hashpw(plaintext, BCrypt.gensalt());
    }
    
    /**
     * @param candidate the clear text
     * @param encryptedPassword the encrypted password string to check.
     * @return true if the candidate matches, false otherwise.
     */
    public static boolean checkPassword(String candidate, String encryptedPassword) {
        if (candidate == null) {
            return false;
        }
        if (encryptedPassword == null) {
            return false;
        }
        return BCrypt.checkpw(candidate, encryptedPassword);
    }
    

}
