/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import chat.Chat;
import chat.ChatTabbedPanel;
import fileInteraction.BoardGameReader;
import fileInteraction.BoardGameWriter;
import java.io.File;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.DefaultListModel;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.Timer;
import lounge.AbstractLoungeModel;
import lounge.LoungeWindowAdapter;
import lounge.gamehub.GameHubModel;
import lounge.gamehub.GameHubPanel;
import lounge.gatheringlounge.FriendList;
import lounge.gatheringlounge.FriendListRenderer;
import lounge.gatheringlounge.GatheringLoungeModel;
import lounge.gatheringlounge.GatheringLoungePanel;
import network.FileContents;
import network.ListenToSocketThread;
import network.NetworkAdapter;
import plugin.GameLoader;
import userManagement.Friend;
import userManagement.FriendStatus;
import userManagement.Player;
import userManagement.User;

public class GameLoungeModel extends AbstractLoungeModel {

	private boolean isHosting;
	private FriendList inviteJList;
	private FriendTeamList playerJList;
	private DefaultListModel friendListModel;
	private ArrayList<Player> invitedPlayerList;
	private ArrayList<Player> playerList;
	private int amountReady;
	private GatheringLoungeModel gatheringLoungeModel;
	private JFrame inviteFrame;
	private JFrame pickGameFrame;
	private JFrame window;
	private ChatTabbedPanel chatPanel;
	//
	private String gameFileName;
	private String gameName;
	private int gamePlayers;
	private int gameTeams;
	private String gameDescription;
	//
	private ExecutorService executor;
	private boolean receivingFase;
	private Timer timer;
	private int ticks;
	//
	public static final String JOIN_TOKEN = "/j";
	public static final String LEAVE_TOKEN = "/l";
	public static final String HOST_TOKEN = "/h";
	public static final String GAME_CHANGED_TOKEN = "/g";
	public static final String GAME_STARTED_TOKEN = "/p";
	public static final String TEAM_CHANGED_TOKEN = "/z";
	public static final String GAME_REQUEST_TOKEN = "/r";
	public static final String GAME_REALLY_STARTED_TOKEN = "/q";
	public static final String KICK_TOKEN = "/k";
	public static final String GAMELOUNGE_NAME = "GameLounge";

	public GameLoungeModel(JFrame window, GatheringLoungeModel gatheringLoungeModel, User currentUser, boolean isHosting, ArrayList<Player> invitedPlayerList) {
		super(window, currentUser);

		((LoungeWindowAdapter) window.getWindowListeners()[0]).setAbstractLoungeModel(this);

		executor = Executors.newCachedThreadPool();

		gameName = "Choose a game, host!";
		gameTeams = 0;
		gamePlayers = 0;
		gameDescription = "No description yet!";

		getCurrentUser().setTeamId(0);

		this.window = window;
		this.isHosting = isHosting;
		this.gatheringLoungeModel = gatheringLoungeModel;

		chatPanel = Chat.getSingleton();
		chatPanel.addChat("GameLounge");

		timer = new Timer(1000, new StartTimer(this));
		receivingFase = false;
		ticks = 5;

		if (isHosting) {
			getCurrentUser().setStatus(FriendStatus.IS_HOSTING);
		} else {
			getCurrentUser().setStatus(FriendStatus.IN_GAMELOUNGE);
		}

		friendListModel = new DefaultListModel();

		playerList = new ArrayList<Player>();
		this.invitedPlayerList = invitedPlayerList;
		for (Player player : invitedPlayerList) {

			final Player speler = player;

			executor.execute(new Runnable() {

				@Override
				public void run() {
					if (NetworkAdapter.getSingleton().getSocketThreadWithIpAndVerifier(speler.getIp().getHostAddress(), speler.getName()) == null) {
						NetworkAdapter.getSingleton().openConnection(speler.getIp().getHostAddress(), speler.getName());
					}

					NetworkAdapter.getSingleton().sendMessage(GameLoungeModel.JOIN_TOKEN + " " + getCurrentUser().getName() + " " + getCurrentUser().getStatus(),
						 speler.getIp().getHostAddress(), speler.getName());
				}
			});

		}

		playerJList = new FriendTeamList(this, friendListModel);
		playerJList.setCellRenderer(new FriendTeamListRenderer(this));

		fireStateChanged();

		amountReady = 1; // De host is altijd ready


		NetworkAdapter.getSingleton().setNetworkListener(this);
	}

	public ChatTabbedPanel getChatPanel() {
		return chatPanel;
	}

	public JList getFriendJList() {
		return playerJList;
	}

	@Override
	public synchronized void receiveData(String networkInput, String fromIp, String fromName, int port) {
		super.receiveData(networkInput, fromIp, fromName, port);

		if (networkInput != null) {

			if (networkInput.startsWith(JOIN_TOKEN)) {

				boolean exists = false;

				Iterator<Player> it = playerList.iterator();
				while (it.hasNext() && !exists) {
					Friend friend = it.next();
					if (friend.getName().equals(fromName)) {
						exists = true;
					}
				}

				if (!exists) {

					Iterator<Player> ite = invitedPlayerList.iterator();
					while (ite.hasNext() && !exists) {

						Player invitedPlayer = ite.next();

						if (invitedPlayer.getName().equals(fromName)) {
							playerList.add(invitedPlayer);
							FriendStatus status = FriendStatus.valueOf(networkInput.split(" ")[2]);
							invitedPlayer.setStatus(status);

							Chat.getSingleton().addChatter(GAMELOUNGE_NAME, invitedPlayer);

							String message = GAME_CHANGED_TOKEN + "@@@";

							message += gameFileName + "@@@";
							message += gameName + "@@@";
							message += gamePlayers + "@@@";
							message += gameTeams + "@@@";
							message += gameDescription;

							NetworkAdapter.getSingleton().sendMessage(message, fromIp, port);

							NetworkAdapter.getSingleton().sendMessage(JOIN_TOKEN + " " + getCurrentUser().getName() + " " + getCurrentUser().getStatus(), fromIp, port);

							fireStateChanged();

							exists = true;
						}

					}

				}

			} else if (networkInput.startsWith(GatheringLoungeModel.I_HAVE_INVITED_TOKEN)) {

				String invitedPlayerName = networkInput.split(" ")[1];
				String invitedPlayerAlias = networkInput.split(" ")[2];
				InetAddress invitedPlayerIp = null;
				try {
					invitedPlayerIp = Inet4Address.getByName(networkInput.split(" ")[3]);
				} catch (UnknownHostException ex) {
					Logger.getLogger(GatheringLoungeModel.class.getName()).log(Level.SEVERE, null, ex);
				}
				int invitedPlayerPort = Integer.parseInt(networkInput.split(" ")[4]);
				FriendStatus invitedPlayerStatus = FriendStatus.valueOf(networkInput.split(" ")[5]);

				Player player = new Player(invitedPlayerName, invitedPlayerAlias, invitedPlayerIp);
				player.setStatus(invitedPlayerStatus);
				invitedPlayerList.add(player);

			} else if (networkInput.startsWith(GAME_STARTED_TOKEN)) {

				if (getCurrentUser().getStatus() == FriendStatus.IN_GAMELOUNGE) {

					leaveGameLounge();

				} else {
					receivingFase = true;

					Chat.getSingleton().addChatMessage(GAMELOUNGE_NAME, "GameInfo", "Teams set. All receive the game!");

					getCurrentUser().setStatus(FriendStatus.IN_GAMELOUNGE);

					for (Friend friend : getCurrentUser().getFriends()) {
						NetworkAdapter.getSingleton().sendMessage(AbstractLoungeModel.STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
							 friend.getIp().getHostAddress(), friend.getName());
					}

					for (Player player : playerList) {
						if (player.getStatus() != FriendStatus.IS_HOSTING) {
							player.setStatus(FriendStatus.IN_GAMELOUNGE);
						}
					}

					amountReady = 1;

					fireStateChanged();

					requestGame();
				}

			} else if (networkInput.startsWith(KICK_TOKEN)) {

				leaveGameLounge();

			} else if (networkInput.startsWith(STATUS_CHANGE_TOKEN)) {

				String status = networkInput.split(" ")[1];
				FriendStatus newState = FriendStatus.valueOf(status);

				for (Friend friend : playerList) {

					if (friend.getName().equals(fromName)) {

						if (newState == FriendStatus.IN_GAMELOUNGE && !receivingFase) {
							amountReady--;
						} else if (newState == FriendStatus.READY || newState == FriendStatus.IS_HOSTING) {
							amountReady++;
						}

						friend.setStatus(newState);

					}
				}

				fireStateChanged();

				if (amountReady == gamePlayers && receivingFase && isHosting && newState == FriendStatus.READY) {
					for (Player player : playerList) {
						NetworkAdapter.getSingleton().sendMessage(GAME_REALLY_STARTED_TOKEN, player.getIp().getHostAddress(), player.getName());
					}

					startStartTimer();
				}

			} else if (networkInput.startsWith(GAME_REALLY_STARTED_TOKEN)) {

				startStartTimer();

			} else if (networkInput.startsWith(LEAVE_TOKEN)) {

				Iterator<Player> iterator = playerList.iterator();
				while (iterator.hasNext()) {
					Friend friend = iterator.next();
					if (friend.getName().equals(fromName)) {
						if (friend.getStatus() == FriendStatus.READY) {
							amountReady--;
						}
						friend.setStatus(FriendStatus.IN_GATHERINGLOUNGE);

						Chat.getSingleton().removeChatter(GAMELOUNGE_NAME, friend);
						iterator.remove();
					}
				}

				fireStateChanged();

			} else if (networkInput.startsWith("LEFT: ")) {

				Iterator<Player> iterator = playerList.iterator();
				while (iterator.hasNext()) {
					Friend friend = iterator.next();
					if (friend.getName().equals(fromName)) {
						if (friend.getStatus() == FriendStatus.READY) {
							amountReady--;
						}
						friend.setStatus(FriendStatus.OFFLINE);

						Chat.getSingleton().removeChatter(GAMELOUNGE_NAME, friend);
						iterator.remove();
					}
				}

				fireStateChanged();

			} else if (networkInput.startsWith(HOST_TOKEN)) {

				JOptionPane.showMessageDialog(null, "The host has left! You are the host now!",
					 "You're hosting!",
					 JOptionPane.INFORMATION_MESSAGE);

				if (getCurrentUser().getStatus() == FriendStatus.READY) {
					amountReady--; // Compensering voor de statuschange
				}

				getCurrentUser().setStatus(FriendStatus.IS_HOSTING);

				for (Friend friend : getCurrentUser().getFriends()) {
					NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
						 friend.getIp().getHostAddress(), friend.getName());
				}

				for (Player player : playerList) {
					NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
						 player.getIp().getHostAddress(), player.getName());
				}

				isHosting = true;

				fireStateChanged();

			} else if (networkInput.startsWith(GAME_CHANGED_TOKEN)) {

				String[] input = networkInput.split("@@@");

				gameFileName = input[1];
				gameName = input[2];
				gamePlayers = Integer.parseInt(input[3]);
				gameTeams = Integer.parseInt(input[4]);
				gameDescription = input[5];

				getCurrentUser().setTeamId(0);
				for (Player player : playerList) {
					player.setTeamId(0);
				}

				fireStateChanged();

			} else if (networkInput.startsWith(TEAM_CHANGED_TOKEN)) {

				int teamid = Integer.parseInt(networkInput.split(" ")[1]);

				for (Player player : playerList) {
					if (player.getName().equals(fromName)) {
						player.setTeamId(teamid);
						break;
					}
				}

				fireStateChanged();

			} else if (networkInput.startsWith(GAME_REQUEST_TOKEN)) {

				if (isHosting) { // Host heeft het spel zeker
					File game = new BoardGameReader().getBoardGame(gameFileName);
					NetworkAdapter.getSingleton().sendSerializableObject(game, fromIp, fromName);
				}
			}
		}
	}

	@Override
	public void receiveFileContents(FileContents file) {
		BoardGameWriter writer = new BoardGameWriter();
		writer.saveBoardGame(file);
		System.out.println("Wordt gesaved naar " + gameFileName);

		amountReady++;
		getCurrentUser().setStatus(FriendStatus.READY);

		for (Player player : playerList) {
			NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
				 player.getIp().getHostAddress(), player.getName());
		}

		for (Friend friend : getCurrentUser().getFriends()) {
			if (friend.getStatus() == FriendStatus.IN_GATHERINGLOUNGE) {
				NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
					 friend.getIp().getHostAddress(), friend.getName());
			}
		}

		fireStateChanged();
	}

	public boolean isReceivingFase() {
		return receivingFase;
	}

	@Override
	public ArrayList<Player> getPlayers() {
		return playerList;
	}

	public boolean isHosting() {
		return isHosting;
	}

	public void switchReady() {
		if (getCurrentUser().getStatus() == FriendStatus.READY) {
			getCurrentUser().setStatus(FriendStatus.IN_GAMELOUNGE);
			amountReady--;
		} else {
			getCurrentUser().setStatus(FriendStatus.READY);
			amountReady++;
		}


		for (Friend friend : playerList) {
			String message = STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus().toString();

			NetworkAdapter.getSingleton().sendMessage(message, friend.getIp().getHostAddress(), friend.getName());
		}

		fireStateChanged();
	}

	public int getAmountReady() {
		return amountReady;
	}

	public void leaveGameLounge() {

		if (!playerList.isEmpty() && isHosting) {
			Collections.shuffle(playerList);
			NetworkAdapter.getSingleton().sendMessage(HOST_TOKEN, playerList.get(0).getIp().getHostAddress(), playerList.get(0).getName());
		}


		for (Friend friend : playerList) {
			String message = LEAVE_TOKEN;

			NetworkAdapter.getSingleton().sendMessage(message, friend.getIp().getHostAddress(), friend.getName());
		}

		getCurrentUser().setStatus(FriendStatus.IN_GATHERINGLOUNGE);

		for (Friend friend : getCurrentUser().getFriends()) {

			if (friend.getStatus() != FriendStatus.OFFLINE) {
				NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(), friend.getIp().getHostAddress(), friend.getName());
			}

		}

		Chat.getSingleton().removeChat("GameLounge");

		gatheringLoungeModel.getPlayerList().clear();
		NetworkAdapter.getSingleton().setNetworkListener(gatheringLoungeModel);
		getWindow().setContentPane(new GatheringLoungePanel(gatheringLoungeModel));
		getWindow().pack();
	}

	public void kickPlayers() {
		Object[] objects = playerJList.getSelectedValues();

		for (int i = 0; i < objects.length; i++) {
			Player player = (Player) objects[i];
			NetworkAdapter.getSingleton().sendMessage(KICK_TOKEN, player.getIp().getHostAddress(), player.getName());
		}
	}

	public void chooseGame() {

		BoardGameReader boardGameReader = new BoardGameReader();
		String[] games = boardGameReader.getBoardGames();

		if (games != null) {
			JList dataList = new JList(games);

			pickGameFrame = new JFrame("Choose the game!");
			GameListPanel gameListPanel = new GameListPanel(this, dataList);
			pickGameFrame.setContentPane(gameListPanel);
			pickGameFrame.pack();
			pickGameFrame.setVisible(true);
		} else {

			JOptionPane.showMessageDialog(null, "You don't have any games :-( Please install one first!",
				 "No games :-(",
				 JOptionPane.INFORMATION_MESSAGE);
		}

	}

	public void pickGame(String name) {
		pickGameFrame.dispose();

		gameFileName = name.substring(0, name.lastIndexOf('.'));

		BoardGameReader boardGameReader = new BoardGameReader();
		File game = boardGameReader.getBoardGame(gameFileName);

		GameLoader gameLoader = new GameLoader(null);
		gameLoader.loadBoardGame(game);

		gameName = gameLoader.getGameName();
		gamePlayers = gameLoader.getNumberOfPlayers();
		gameTeams = gameLoader.getNumberOfTeams();
		gameDescription = gameLoader.getGameDescription();

		String message = GAME_CHANGED_TOKEN + "@@@";
		message += gameFileName + "@@@";
		message += gameName + "@@@";
		message += gamePlayers + "@@@";
		message += gameTeams + "@@@";
		message += gameDescription;

		for (Friend friend : playerList) {
			NetworkAdapter.getSingleton().sendMessage(message, friend.getIp().getHostAddress(), friend.getName());
		}

		fireStateChanged();

	}

	public void openInviteFrame() {
		inviteFrame = new JFrame("Invite friends from gatheringlounge");

		JPanel panel = new InvitePanel(this, getInviteJList());

		inviteFrame.setContentPane(panel);
		inviteFrame.pack();
		inviteFrame.setVisible(true);
	}

	public JList getInviteJList() {
		friendListModel = new DefaultListModel();

		inviteJList = new FriendList(this, friendListModel);
		inviteJList.setCellRenderer(new FriendListRenderer());

		inviteJList.stateChanged(null);

		return inviteJList;
	}

	public void invitePlayers(JList friendList) {
		Object[] friends = friendList.getSelectedValues();

		inviteFrame.dispose();

		for (int i = 0; i < friends.length; i++) {

			Friend friend = (Friend) friends[i];

			for (Player player : invitedPlayerList) {

				if (!player.getName().equals(friend.getName())) {
					NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.I_HAVE_INVITED_TOKEN + " " + friend.getName() + " " + friend.getAlias() + " " + friend.getIp().getHostAddress() + " " + friend.getStatus().toString(), player.getIp().getHostAddress(), player.getName());
				}
			}
		}

		for (int i = 0; i < friends.length; i++) {
			Friend friend = (Friend) friends[i];

			for (Player player : invitedPlayerList) {
				NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.I_HAVE_INVITED_TOKEN + " " + player.getName() + " " + player.getAlias() + " " + player.getIp().getHostAddress() + " " + player.getStatus().toString(), friend.getIp().getHostAddress(), friend.getName());
			}

			NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.INVITE_TOKEN + " " + super.getCurrentUser().getName(),
				 friend.getIp().getHostAddress(), friend.getName());

			Player player = new Player(friend.getName(), friend.getAlias(), friend.getIp());
			player.setStatus(friend.getStatus());
			invitedPlayerList.add(player);
		}

	}

	public void setTeam(int i) {
		getCurrentUser().setTeamId(i);

		for (Friend friend : playerList) {
			NetworkAdapter.getSingleton().sendMessage(TEAM_CHANGED_TOKEN + " " + i, friend.getIp().getHostAddress(), friend.getName());
		}

		fireStateChanged();
	}

	public void startGame() {
		amountReady = 1;

		fireStateChanged();

		receivingFase = true;

		Chat.getSingleton().addChatMessage(GAMELOUNGE_NAME, "GameInfo", "Games are being distributed...");

		for (Player player : playerList) {
			NetworkAdapter.getSingleton().sendMessage(GAME_STARTED_TOKEN, player.getIp().getHostAddress(), player.getName());

		}
	}

	//////
	// Getters & setters
	//////
	public String getGameDescription() {
		return gameDescription;
	}

	public String getGameName() {
		return gameName;
	}

	public int getGamePlayers() {
		return gamePlayers;
	}

	public int getGameTeams() {
		return gameTeams;
	}

	@Override
	public ArrayList<Friend> getFriends() {
		ArrayList<Friend> availableFriends = new ArrayList<Friend>();

		for (Friend friend : getCurrentUser().getFriends()) {
			if (friend.getStatus() == FriendStatus.IN_GATHERINGLOUNGE) {
				availableFriends.add(friend);
			}
		}

		return availableFriends;
	}

	private void requestGame() {

		if (new BoardGameReader().getBoardGame(gameFileName) == null) {

			for (Player player : playerList) {
				if (player.getStatus() == FriendStatus.IS_HOSTING) {
					NetworkAdapter.getSingleton().sendMessage(GAME_REQUEST_TOKEN + " " + gameFileName, player.getIp().getHostAddress(), player.getName());
				}
			}

		} else {

			amountReady++;
			getCurrentUser().setStatus(FriendStatus.READY);
			fireStateChanged();

			for (Player player : playerList) {
				NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(), player.getIp().getHostAddress(), player.getName());
				NetworkAdapter.getSingleton().sendChatMessage(getCurrentUser().getAlias() + " I have the game!", GAMELOUNGE_NAME, player.getIp().getHostAddress(), player.getName());
			}
		}
	}

	private void startStartTimer() {
		timer.start();
		System.out.println("Starting zeh timer!");
	}

	public void tick() {
		Chat.getSingleton().addChatMessage(GAMELOUNGE_NAME, "GameInfo", "Starting the game in: " + ticks + "...");
		ticks--;
		if (ticks == 0) {
			System.out.println("Stopping zeh timer!");
			timer.stop();
			ticks = 5;
			reallyStartGame();
		}
	}

	private void reallyStartGame() {
		openGameHub(isHosting);
	}

	public void openGameHub(boolean isHost) {
		getCurrentUser().setStatus(FriendStatus.IN_GAME);

		for (Friend player : getCurrentUser().getFriends()) {
			NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
				 player.getIp().getHostAddress(), player.getName());
		}

		Chat.getSingleton().removeChat(GAMELOUNGE_NAME);

		GameHubModel gameHubModel = new GameHubModel(window, gatheringLoungeModel, getCurrentUser(), gameFileName, gamePlayers, playerList);
		GameHubPanel gameHubPanel = new GameHubPanel(gameHubModel);

		getWindow().setContentPane(gameHubPanel);
		getWindow().pack();
	}

	public void installGame() {
		BoardGameReader boardGameReader = new BoardGameReader();
		File file = boardGameReader.getBoardGame();

		if (file != null) {
			BoardGameWriter boardGameWriter = new BoardGameWriter();
			boardGameWriter.saveBoardGame(file);

			JOptionPane.showMessageDialog(null, "Game installed!",
				 "Succes!",
				 JOptionPane.INFORMATION_MESSAGE);
		}
	}

	@Override
	public void windowClosed() {
		leaveGameLounge();
	}
}
