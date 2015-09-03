package fileInteraction;

import java.io.File;
import network.FileContents;
import userManagement.User;

/**
 *
 * @author Dieter Decaestecker
 */
public interface FileInterface 
{
    public void saveBoardGame(FileContents game);
    public void saveBoardGame(File game);
    public File getBoardGame(String gamename);
    public void addNewUser(User newUser) throws UserExistsException;
    public void deleteUser(String username) throws UserNotFoundException;
    public void adjustUser(User changedUser) throws UserNotFoundException;
    public User readUser(String username) throws UserNotFoundException;
    public boolean userExists(String username);
}
