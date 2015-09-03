package plugin;
import java.io.File;
import java.util.ArrayList;
import java.util.GregorianCalendar;

import javax.swing.JPanel;
import plugin.GameState;
import userManagement.PlayerInterface;
/**
 *
 * @author Sander Demeester
 */
public abstract class AbstractGameLoader {

	public void loadBoardGame(File gameFile) {
	}
	public JPanel getGui() {
		return null;
	}
	public GameState getCurrentGameState() {
		return null;
	}
	public String getGameDescription() {
		return null;
	}
	public String getGameRules() {
		return null;
	}
	public String getGameName() {
		return null;
	}
	public int getNumberOfPlayers() {
		return 0;
	}
	public int getNumberOfTeams() {
		return 0;
	}
	
	public PlayerInterface getCurrentUser() {
		return null;
	}
	public ArrayList<PlayerInterface> getUsersInGame() {
		return null;
	}
	public void gameStateRecieved(GameState state, PlayerInterface player) {
	}
	public void sendGameState(GameState state, PlayerInterface player) {
	}
	public void playerLeft(PlayerInterface playerLeft) {
	}
	public void closeGame() {
	}
    public void addHighScore(int score, GregorianCalendar date, String game) {
	}
    public void startGame() throws Exception{ //fout tijdens starten van spel.
    	
    }
    

}
