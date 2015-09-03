package fileInteraction;

import java.io.File;
import network.FileContents;
import plugin.BoardGame;
import userManagement.User;

/**
 * @author NVH
 * @filename FileImplementation.java
 */
public class FileImplementation implements FileInterface{

    private BoardGameWriter bgw;
    private BoardGameReader bgr;
    private UserFileWriter  ufw;
    private UserFileReader  ufr;

    public FileImplementation(String gamePathName, String userPathName) {
	File gameFile = new File(gamePathName); 
	bgw = new BoardGameWriter();
	bgr = new BoardGameReader();
	
	File userFile = new File(userPathName);
	ufw = new UserFileWriter();
	ufr = new UserFileReader();
    }
    
    /**
     * BoardGame opslaan naar Jar-file
     * @param game  het op te slaan spel
     */
    @Override
    public void saveBoardGame(FileContents game){
	if(game != null){
	    bgw.saveBoardGame(game);
	}
    }

    
    @Override
    public void saveBoardGame(File game){
	if(game != null){
	    bgw.saveBoardGame(game);
	}
    }
    /**
     * Ophalen van BoardGame uit het game-bestand
     * @param gameName	de naam van het op te halen spel
     * @return	het gezochte spel als BoardGame
     */
    @Override
    public File getBoardGame(String gameName) {
	return bgr.getBoardGame(gameName);
    }

    @Override
    public void addNewUser(User newUser) throws UserExistsException{
	if(!userExists(newUser.getName())) {
	    ufw.addNewUser(newUser);
	}else{
	    throw new UserExistsException();
	}
    }

    @Override
    public void deleteUser(String username) throws UserNotFoundException{
	if(userExists(username)) {
	    ufw.deleteUser(username);
	}else{
	    throw new UserNotFoundException(username);
	}
    }

    @Override
    public void adjustUser(User changedUser) throws UserNotFoundException{
	if(userExists(changedUser.getName())) {
	    ufw.adjustUser(changedUser);
	}else{
	    throw new UserNotFoundException(changedUser.getName());
	}
    }

    @Override
    public User readUser(String username) throws UserNotFoundException {
	User user = null;
	if(!userExists(username)) {
	   user = ufr.readUser(username);
	}else{
	    throw new UserNotFoundException(username);
	}
	return user;
    }

    @Override
    public boolean userExists(String username){
	return ufr.userExists(username);
    }

}
