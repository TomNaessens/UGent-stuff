package plugin;

import java.io.File;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.GregorianCalendar;
import javax.swing.JPanel;
import lounge.gamehub.GameHubModel;
import network.NetworkAdapter;
import userManagement.HighScore;
import userManagement.Player;
import userManagement.PlayerInterface;

public class GameLoader extends AbstractGameLoader {

	private GameState currentGameState = null;
	private File file;
	private BoardGame game;
	private GameHubModel gamehub;
	private Class classToLoad;
	private Object gameObject;

	public GameLoader(GameHubModel gamehub) {
		this.gamehub = gamehub;
	}

	private void loadJarFile() throws Exception {

		URLClassLoader child = new URLClassLoader (new URL[] {file.toURL()},
				this.getClass().getClassLoader());
		classToLoad = Class.forName("plugin.Setup",true,child);
		gameObject = classToLoad.newInstance ();
	}
	@Override
	public void startGame() throws Exception {
		Class[] argumenten = new Class[] {GameLoader.class};
		GameLoader mainArgumenten = this;
		Method method = classToLoad.getDeclaredMethod ("setup", argumenten);
		game = (BoardGame)method.invoke (gameObject,(Object)mainArgumenten);
		
	}
	@Override
	public void loadBoardGame(File file) {
		this.file = file;
		try {
			loadJarFile();
		} catch (Exception e) {
			System.out.println(e);
		}
	}

	@Override
	public JPanel getGui() { return game.getPaneel(); }

	@Override
	public String getGameDescription() {
		try{
		Method m = classToLoad.getDeclaredMethod("getGameDescription",null);
		return (String)(m.invoke(gameObject, null));
		}catch(Exception e){ //papapapak ze dan, rescu rangers.
			e.printStackTrace();
			return "";
		}
	}

	@Override
	public String getGameRules() { 
		try{
			Method m = classToLoad.getDeclaredMethod("getGameRules", null);
			return (String)(m.invoke(gameObject, null));
		}catch(Exception e){
			e.printStackTrace();
			return "";
		}
	}

	@Override
	public String getGameName() { 
		try{
			Method m = classToLoad.getDeclaredMethod("getNameGame", null);
			return (String)(m.invoke(gameObject, null));
		}catch(Exception e){
			e.printStackTrace();
			return "";
		}
	}

	@Override
	public int getNumberOfPlayers() { 
		try{
			Method m = classToLoad.getDeclaredMethod("getNumberofplayer", null);
			return (Integer)(m.invoke(gameObject, null));
		}catch(Exception e){
			e.printStackTrace();
			return 0;
		}
	}
	
	@Override
	public int getNumberOfTeams() { 
		try{
			Method m = classToLoad.getDeclaredMethod("getNumberofteams",null);
			return (Integer)(m.invoke(gameObject, null));
		}catch(Exception e){
			e.printStackTrace();
			return 0;
		}
	}

	@Override
	public PlayerInterface getCurrentUser() {
		if(gamehub == null){
			System.out.println("running in test mode, constructing test player.");
			return new Player("Test-user", "Test-user",null);
		}
		return (PlayerInterface)gamehub.getCurrentUser(); 
	}

	@Override
	public ArrayList<PlayerInterface> getUsersInGame() {
		ArrayList<PlayerInterface> playerList = new ArrayList<PlayerInterface>();
		if(gamehub != null){
			for(PlayerInterface p : gamehub.getPlayers()){
				playerList.add(p);
			}
			return playerList;
		}else{
			ArrayList<PlayerInterface> l = new ArrayList<PlayerInterface>();
			l.add(new Player("debug-mode", "DEBUG", null));
			return l;
		}
	}

	@Override
	public void gameStateRecieved(GameState state, PlayerInterface player) {
		currentGameState = state;
		System.out.println("ontvang: " + currentGameState.getInfo());
		game.update(currentGameState, player);
	}

	@Override
	public void playerLeft(PlayerInterface playerLeft) { game.playerLeft(playerLeft); }

	@Override
	public void closeGame() { gamehub.gameFinished(); }

	/**
	 * Deze methode wordt door een spel gebruikt om een gameState te versturen 
	 * naar een specefieke player.
	 */
	@Override
	public void sendGameState(GameState state, PlayerInterface player) {
		System.out.println("verstuur: " + "/x"+state.getInfo());
		NetworkAdapter.getSingleton().sendMessage("/x"+state.getInfo(),
				((Player)player).getIp().getHostAddress(), ((Player)player).getName());

	}

	@Override
	public void addHighScore(int score, GregorianCalendar date, String game) {
		gamehub.getCurrentUser().addHighScore(new HighScore(score, date,game));

	}

	@Override
	public GameState getCurrentGameState() { return currentGameState; }
}
