/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamehub;

import chat.Chat;
import chat.ChatTabbedPanel;
import fileInteraction.BoardGameReader;
import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import javax.swing.JFrame;
import javax.swing.JPanel;
import lounge.AbstractLoungeModel;
import lounge.LoungeWindowAdapter;
import lounge.gatheringlounge.GatheringLoungeModel;
import lounge.gatheringlounge.GatheringLoungePanel;
import network.NetworkAdapter;
import plugin.AbstractGameLoader;
import plugin.GameLoader;
import plugin.GameState;
import userManagement.Friend;
import userManagement.FriendStatus;
import userManagement.Player;
import userManagement.User;

public class GameHubModel extends AbstractLoungeModel {

	private JFrame window;
	private ChatTabbedPanel chatTabbedPanel;
	private ArrayList<Player> playerList;
	private int gamePlayers;
	private AbstractGameLoader gameLoader;
	private GatheringLoungeModel gatheringLoungeModel;
	private JPanel gameGui;
	public static final String GAME_UPDATE_TOKEN = "/x";
	public static final String PLAYER_LEFT_TOKEN = "/µ";
	public static final String GAMEHUB_NAME = "GameHub";

	public GameHubModel(JFrame window, GatheringLoungeModel gatheringLoungeModel, User currentUser, String gameFileName, int gamePlayers, ArrayList<Player> playerList) {
		super(window, currentUser);

		((LoungeWindowAdapter) window.getWindowListeners()[0]).setAbstractLoungeModel(this);

		this.window = window;
		this.gamePlayers = gamePlayers;

		gameLoader = null;

		this.gatheringLoungeModel = gatheringLoungeModel;
		
		this.playerList = playerList;
		playerList.add((Player) getCurrentUser());
		Collections.sort(playerList, new CompareByTeam());

		chatTabbedPanel = Chat.getSingleton();
		Chat.getSingleton().addChat(GameHubModel.GAMEHUB_NAME);
		Chat.getSingleton().addChat(GameHubModel.GAMEHUB_NAME + ": Team " + getCurrentUser().getTeamId());

		for (Player player : playerList) {
			Chat.getSingleton().getChatTabbedModel().addChatter(GameHubModel.GAMEHUB_NAME, player);

			if (player.getTeamId() == getCurrentUser().getTeamId()) {
				Chat.getSingleton().getChatTabbedModel().addChatter(GameHubModel.GAMEHUB_NAME + ": Team " + getCurrentUser().getTeamId(), player);
			}
		}


		BoardGameReader boardGameReader = new BoardGameReader();
		File game = boardGameReader.getBoardGame(gameFileName);

		gameLoader = new GameLoader(this);
		gameLoader.loadBoardGame(game);
		try {
			gameLoader.startGame();
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		gameGui = gameLoader.getGui();

		NetworkAdapter.getSingleton().setNetworkListener(this);
	}

	@Override
	public synchronized void receiveData(String networkInput, String fromIp, String fromName, int port) {
		super.receiveData(networkInput, fromIp, fromName, port);

		if (networkInput.startsWith(GAME_UPDATE_TOKEN)
			 && gameLoader != null) {

			GameState state = new GameState(networkInput.substring(2));

			for (Player player : playerList) {
				if (player.getName().equals(fromName)) {
					gameLoader.gameStateRecieved(state, player);
				}
			}
			
		} else if (networkInput.startsWith("LEFT: ")) {
			
			Iterator<Player> it = playerList.iterator();
			boolean found = false;
			
			while(it.hasNext() && !found) {
				Player player = it.next();
				if (player.getName().equals(fromName)) {
					found = true;
					
					gameLoader.playerLeft(player);
					it.remove();
				}
			}
		}
	}

	public void sendMessage(Object object, Player player) {
		NetworkAdapter.getSingleton().sendSerializableObject(object, player.getIp().getHostAddress(), player.getName());
	}

	public void gameFinished() {
		getCurrentUser().setStatus(FriendStatus.IN_GATHERINGLOUNGE);

		for (Friend friend : getCurrentUser().getFriends()) {

			if (friend.getStatus() != FriendStatus.OFFLINE) {
				NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(), friend.getIp().getHostAddress(), friend.getName());
			}

		}

		Chat.getSingleton().removeChat("GameHub");
		Chat.getSingleton().removeChat(GameHubModel.GAMEHUB_NAME + ": Team " + getCurrentUser().getTeamId());

		gatheringLoungeModel.getPlayerList().clear();
		NetworkAdapter.getSingleton().setNetworkListener(gatheringLoungeModel);
		getWindow().setContentPane(new GatheringLoungePanel(gatheringLoungeModel));
		getWindow().pack();
	}

	@Override
	public ArrayList<Friend> getFriends() {
		return null;
	}

	@Override
	public ArrayList<Player> getPlayers() {
		return playerList;
	}

	public ChatTabbedPanel getChatTabbedPanel() {
		return chatTabbedPanel;
	}

	public JPanel getGameGui() {
		return gameGui;
	}

	public int getGamePlayers() {
		return gamePlayers;
	}
}
