/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import chat.Chat;
import chat.ChatTabbedPanel;
import fileInteraction.UserFileWriter;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
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
import lounge.AbstractLoungeModel;
import lounge.LoungeWindowAdapter;
import lounge.gamelounge.GameLoungeModel;
import lounge.gamelounge.GameLoungePanel;
import network.NetworkAdapter;
import userManagement.Friend;
import userManagement.FriendStatus;
import userManagement.HighScore;
import userManagement.Player;
import userManagement.User;

public class GatheringLoungeModel extends AbstractLoungeModel {

	private JList userList;
	private ArrayList<Player> invitedPlayerList;
	private int hostPort;
	private DefaultListModel friendListModel;
	private JFrame addFriendFrame;
	private JFrame editFriendFrame;
	ExecutorService executor;
	private String playerName;
	private String playerAlias;
	private String playerScore;
	private ChatTabbedPanel chatPanel;
	public static final String INVITE_TOKEN = "/i";
	public static final String FRIEND_REQUEST_TOKEN = "/fr";
	public static final String FRIEND_ACCEPT_TOKEN = "/fa";
	public static final String GATHERINGLOUNGE_NAME = "GatheringLounge";
	public static final String I_HAVE_INVITED_TOKEN = "/a";
	public static final String REQUEST_PROFILE_TOKEN = "/ù";
	public static final String RECEIVE_PROFILE_TOKEN = "/°";

	public GatheringLoungeModel(JFrame window, User currentUser) {
		super(window, currentUser);
		
		((LoungeWindowAdapter) window.getWindowListeners()[0]).setAbstractLoungeModel(this);

		executor = Executors.newCachedThreadPool();

		// Bugfix: zet alle statussen op offline (fix voor de edituser die de users kopieert)
		for (Friend friend : getCurrentUser().getFriends()) {
			friend.setStatus(FriendStatus.OFFLINE);
		}

		NetworkAdapter.getSingleton().startHosting(currentUser.getName());
		hostPort = NetworkAdapter.getSingleton().getPortBeingHostedOn();

		playerScore = "";
		
		chatPanel = Chat.getSingleton();
		Chat.getSingleton().getChatTabbedModel().setUser(currentUser);
		Chat.getSingleton().addChat(GatheringLoungeModel.GATHERINGLOUNGE_NAME);

		invitedPlayerList = new ArrayList<Player>();

		Iterator<Friend> iterator = currentUser.getFriends().iterator();
		while (iterator.hasNext()) {
			final Friend friend = iterator.next();
			executor.execute(new Runnable() {

				@Override
				public void run() {
					NetworkAdapter.getSingleton().openConnection(friend.getIp().getHostAddress(), friend.getName());
				}
			});
		}

		NetworkAdapter.getSingleton().setNetworkListener(this);
	}

	public int getHostPort() {
		return hostPort;
	}

	@Override
	public synchronized void receiveData(String networkInput, String fromIp, String fromName, int port) {
		super.receiveData(networkInput, fromIp, fromName, port);


		if (networkInput != null) {
			if (networkInput.startsWith(INVITE_TOKEN)) {

				String vanUser = networkInput.split(" ")[1];

				int confirmed = JOptionPane.showConfirmDialog(null,
					 vanUser + " invites you to play a game accept? ", "Warning",
					 JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null);
				if (confirmed == JOptionPane.YES_OPTION) {

					for (Friend friend : getCurrentUser().getFriends()) {
						if (friend.getName().equals(vanUser)) {
							Player player = new Player(friend.getName(), friend.getAlias(), friend.getIp());
							player.setStatus(friend.getStatus());
							invitedPlayerList.add(player);
						}
					}

					openGameLounge(false);
				} else {
					invitedPlayerList.clear();
				}

			} else if (networkInput.startsWith(I_HAVE_INVITED_TOKEN)) {

				String invitedPlayerName = networkInput.split(" ")[1];
				String invitedPlayerAlias = networkInput.split(" ")[2];
				InetAddress invitedPlayerIp = null;
				try {
					invitedPlayerIp = Inet4Address.getByName(networkInput.split(" ")[3]);
				} catch (UnknownHostException ex) {
					Logger.getLogger(GatheringLoungeModel.class.getName()).log(Level.SEVERE, null, ex);
				}
				FriendStatus invitedPlayerStatus = FriendStatus.valueOf(networkInput.split(" ")[4]);

				Player player = new Player(invitedPlayerName, invitedPlayerAlias, invitedPlayerIp);
				player.setStatus(invitedPlayerStatus);
				invitedPlayerList.add(player);

			} else if (networkInput.startsWith(RECEIVE_PROFILE_TOKEN)) {

				String[] input = networkInput.split(" ");

				String deel = input[1];

				if (deel.equals("begin")) {

					playerName = input[2];
					playerAlias = input[3];

				} else if (deel.equals("score")) {

					playerScore += input[2];
					for (int i = 3; i < input.length; i++) {
						playerScore += " " + input[i];
					}
					playerScore += "\n";

				} else { // Einde
					showProfile(playerName, playerAlias, playerScore);
				}

			} else if (networkInput.startsWith(NAME_CHANGE_TOKEN)) {

				Iterator<Friend> iterator = super.getCurrentUser().getFriends().iterator();
				while (iterator.hasNext()) {
					Friend friend = iterator.next();

					String newAlias = networkInput.split(" ")[1];

					if (friend.getName().equals(fromName)) {
						Chat.getSingleton().getChatTabbedModel().editChatter(friend, friend.getAlias(), newAlias);
						friend.setAlias(newAlias);
					}
				}

				saveUser();
				fireStateChanged();

			} else if (networkInput.startsWith(FRIEND_REQUEST_TOKEN)) {
				Iterator<Friend> iterator = super.getCurrentUser().getFriends().iterator();
				boolean exists = false;

				String name = networkInput.split(" ")[1];
				String alias = networkInput.split(" ")[2];

				Friend friend = null;

				while (iterator.hasNext() && !exists) {
					friend = iterator.next();

					if (friend.getName().equals(fromName)) {
						exists = true;
					}
				}

				if (!exists) {	// maak vriend aan
					openAddFriendFrame(name, alias, fromIp, port);
				} else {
					NetworkAdapter.getSingleton().sendMessage(FRIEND_ACCEPT_TOKEN + " " + getCurrentUser().getName() + " " + getCurrentUser().getAlias(), fromIp, port);
					friend.setStatus(FriendStatus.IN_GATHERINGLOUNGE);
					Chat.getSingleton().addChatter(GATHERINGLOUNGE_NAME, friend);
					fireStateChanged();
				}

			} else if (networkInput.startsWith("LEFT:")) {

				for (Friend friend : getCurrentUser().getFriends()) {
					if (friend.getName().equals(fromName)) {
						Chat.getSingleton().removeChatter(GATHERINGLOUNGE_NAME, friend);
					}
				}

			} else if (networkInput.startsWith(GameLoungeModel.STATUS_CHANGE_TOKEN)) {

				for (Friend friend : getCurrentUser().getFriends()) {
					if (friend.getName().equals(fromName)) {

						FriendStatus friendStatus = friend.getStatus();

						if (friendStatus == FriendStatus.IN_GATHERINGLOUNGE) {
							Chat.getSingleton().addChatter(GATHERINGLOUNGE_NAME, friend);
						}
					}
				}

			} else if (networkInput.startsWith(FRIEND_ACCEPT_TOKEN)) {

				String name = networkInput.split(" ")[1];
				String alias = networkInput.split(" ")[2];
				String ip = fromIp;

				JOptionPane.showMessageDialog(null,
					 name + " (IP: " + ip + ") has accepted your friend request.", "Friend request accepted",
					 JOptionPane.INFORMATION_MESSAGE, null);

				try {
					Friend friend = new Friend(name, alias, Inet4Address.getByName(ip));
					Chat.getSingleton().addChatter(GATHERINGLOUNGE_NAME, friend);
					getCurrentUser().getFriends().add(friend);
					saveUser();

					friend.setStatus(FriendStatus.IN_GATHERINGLOUNGE);
					fireStateChanged();

				} catch (UnknownHostException ex) {
					System.out.println("Zou niet mogen gebeuren.");
				}

			}
		}
	}

	public JList getFriendJList() {
		friendListModel = new DefaultListModel();

		userList = new FriendList(this, friendListModel);
		userList.setCellRenderer(new FriendListRenderer());

		fireStateChanged();

		return userList;
	}

	public void openAddFriendFrame() {
		addFriendFrame = new JFrame("Add friend");
		JPanel panel = new AddFriendPanel(this);
		addFriendFrame.setContentPane(panel);
		addFriendFrame.pack();
		addFriendFrame.setVisible(true);

		addFriendFrame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
	}

	public void openAddFriendFrame(String name, String alias, String ip, int port) {

		int confirmed = JOptionPane.showConfirmDialog(null,
			 name + " (IP: " + ip + ") tries to add you: accept? ", "Friend request",
			 JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null);
		if (confirmed == JOptionPane.YES_OPTION) {
			try {
				Friend friend = new Friend(name, alias, Inet4Address.getByName(ip));

				getCurrentUser().getFriends().add(friend);

				saveUser();

				friend.setStatus(FriendStatus.IN_GATHERINGLOUNGE);

				Chat.getSingleton().addChatter(GATHERINGLOUNGE_NAME, friend);
				fireStateChanged();

				NetworkAdapter.getSingleton().sendMessage(FRIEND_ACCEPT_TOKEN + " " + getCurrentUser().getName() + " " + getCurrentUser().getAlias(), ip, port);

			} catch (UnknownHostException ex) {
				System.out.println("Zou niet mogen gebeuren.");
			}
		} else {
			NetworkAdapter.getSingleton().closeConnection(ip, port);
		}

	}

	void openEditFriendFrame() {
		Friend friend = (Friend) userList.getSelectedValue();

		editFriendFrame = new JFrame("Edit friend");
		JPanel panel = new EditFriendPanel(friend, this);
		editFriendFrame.setContentPane(panel);
		editFriendFrame.pack();
		editFriendFrame.setVisible(true);
	}

	public void closeFriendFrame() {
		addFriendFrame.dispose();
	}

	public void deleteFriend() {
		Object[] selectedFriends = userList.getSelectedValues();
		for (int i = 0; i < selectedFriends.length; i++) {
			Friend friend = (Friend) selectedFriends[i];
			if (friend.getStatus() != FriendStatus.OFFLINE) {
				NetworkAdapter.getSingleton().sendKillCommand(friend.getIp().getHostAddress(), friend.getName());
				NetworkAdapter.getSingleton().closeConnection(friend.getIp().getHostAddress(), friend.getName());
				Chat.getSingleton().removeChatter(GATHERINGLOUNGE_NAME, friend);
			}
			super.getCurrentUser().getFriends().remove(friend);
		}

		saveUser();

		fireStateChanged();
	}

	public void saveUser() {
		UserFileWriter userFileWriter = new UserFileWriter();
		userFileWriter.adjustUser(super.getCurrentUser());
	}

	public void editFriend(Friend friend, final String friendIp) {
		Iterator<Friend> iterator = super.getCurrentUser().getFriends().iterator();
		boolean friendExists = false;

		while (iterator.hasNext() && !friendExists) {
			if (iterator.next().getIp().getHostAddress().equals(friendIp)) {
				friendExists = true;
			}
		}

		if ("".equals(friendIp)) {
			JOptionPane.showMessageDialog(null, "Please enter an IP-address.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else if (friendExists && !friend.getIp().getHostAddress().equals(friendIp)) {
			JOptionPane.showMessageDialog(null, "You've already added that user as friend.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else {
			try {
				String backupName = friend.getAlias();
				String backupIp = friend.getIp().getHostAddress();

				friend.setIp(Inet4Address.getByName(friendIp));

				editFriendFrame.dispose();

				saveUser();

				fireStateChanged();

				JOptionPane.showMessageDialog(
					 null,
					 backupName + "'s IP has been changed from " + backupIp + " to " + friendIp,
					 "Friend requested",
					 JOptionPane.INFORMATION_MESSAGE);

				// Sluit de connectie en heropent naar het andere IP-adres
				NetworkAdapter.getSingleton().closeConnection(backupIp, friend.getName());

				final Friend vriend = friend;
				executor.execute(new Runnable() {

					@Override
					public void run() {
						NetworkAdapter.getSingleton().openConnection(friendIp, vriend.getName());
					}
				});


			} catch (UnknownHostException ex) {
				JOptionPane.showMessageDialog(null, "Please specify a valid IP-adress.",
					 "Error",
					 JOptionPane.ERROR_MESSAGE);
			}
		}
	}

	public void addFriend(final String name, final String ip) {
		Iterator<Friend> iterator = super.getCurrentUser().getFriends().iterator();
		boolean friendExists = false;

		while (iterator.hasNext() && !friendExists) {
			if (iterator.next().getName().equals(name)) {
				friendExists = true;
			}
		}

		if ("".equals(ip)) {
			JOptionPane.showMessageDialog(null, "Please enter an IP-address.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else if (friendExists) {
			JOptionPane.showMessageDialog(null, "You've already added that user as friend.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else {
			try {

				executor.execute(new Runnable() {

					@Override
					public void run() {
						NetworkAdapter.getSingleton().openConnection(ip, name);
						NetworkAdapter.getSingleton().sendMessage(FRIEND_REQUEST_TOKEN + " "
							 + getCurrentUser().getName() + " " + getCurrentUser().getAlias(), ip, name);

					}
				});


				addFriendFrame.dispose();

				Inet4Address.getByName(ip);

				JOptionPane.showMessageDialog(null, "A friend request has been sent to " + ip,
					 "Friend added",
					 JOptionPane.INFORMATION_MESSAGE);

			} catch (NumberFormatException ex) {
				JOptionPane.showMessageDialog(null, "Please specify a valid port-number.",
					 "Error",
					 JOptionPane.ERROR_MESSAGE);
			} catch (UnknownHostException ex) {
				JOptionPane.showMessageDialog(null, "Please specify a valid IP-adress.",
					 "Error",
					 JOptionPane.ERROR_MESSAGE);
			}
		}
	}

	@Override
	public ArrayList<Friend> getFriends() {
		return super.getCurrentUser().getFriends();
	}

	public void host() {

		// Invite selected friends
		Object[] selectedFriends = userList.getSelectedValues();

		getCurrentUser().setStatus(FriendStatus.IS_HOSTING);

		ArrayList<Friend> friends = getCurrentUser().getFriends();
		for (Friend friend : friends) {
			if (friend.getStatus() != FriendStatus.OFFLINE) {
				NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
					 friend.getIp().getHostAddress(), friend.getName());
			}
		}

		for (int i = 0; i < selectedFriends.length; i++) {
			Friend friend = (Friend) selectedFriends[i];

			for (int j = 0; j < selectedFriends.length; j++) {

				Friend vriend = (Friend) selectedFriends[j];

				if (friend != vriend) {
					NetworkAdapter.getSingleton().sendMessage(I_HAVE_INVITED_TOKEN + " " + friend.getName() + " " + friend.getAlias() + " " + friend.getIp().getHostAddress() + " " + friend.getStatus().toString(), vriend.getIp().getHostAddress(), vriend.getName());
				}

			}
		}

		for (int i = 0; i < selectedFriends.length; i++) {
			Friend friend = (Friend) selectedFriends[i];

			NetworkAdapter.getSingleton().sendMessage(INVITE_TOKEN + " " + super.getCurrentUser().getName(),
				 friend.getIp().getHostAddress(), friend.getName());

			Player player = new Player(friend.getName(), friend.getAlias(), friend.getIp());
			player.setStatus(friend.getStatus());
			invitedPlayerList.add(player);

		}

		openGameLounge(true);

	}

	public ArrayList<Player> getPlayerList() {
		return invitedPlayerList;
	}

	public void openGameLounge(boolean isHost) {

		if (!isHost) {
			getCurrentUser().setStatus(FriendStatus.IN_GAMELOUNGE);

			for (Friend friend : getCurrentUser().getFriends()) {

				if (friend.getStatus() != FriendStatus.OFFLINE) {
					NetworkAdapter.getSingleton().sendMessage(STATUS_CHANGE_TOKEN + " " + getCurrentUser().getStatus(),
						 friend.getIp().getHostAddress(), friend.getName());
				}
			}
		}

		GameLoungeModel gameLoungeModel = new GameLoungeModel(super.getWindow(), this, super.getCurrentUser(), isHost, invitedPlayerList);
		GameLoungePanel gameLoungePanel = new GameLoungePanel(gameLoungeModel);

		super.getWindow().setContentPane(gameLoungePanel);
		super.getWindow().pack();

	}

	@Override
	public ArrayList<Player> getPlayers() {
		return null;
	}

	public ChatTabbedPanel getChatPanel() {
		return chatPanel;
	}

	public void requestProfile() {
		Friend friend = (Friend) userList.getSelectedValue();

		if (friend.getStatus() != FriendStatus.OFFLINE) {
			NetworkAdapter.getSingleton().sendMessage(REQUEST_PROFILE_TOKEN, friend.getIp().getHostAddress(), friend.getName());
		}
	}

	public void showProfile(String playerName, String playerAlias, String playerScore) {
		JFrame frame = new JFrame("Profile");
		JPanel profilePanel = new ProfilePanel(playerName, playerAlias, playerScore);
		frame.setContentPane(profilePanel);
		frame.pack();
		frame.setVisible(true);
		
		this.playerScore = "";
	}

	public void viewProfile() {
		receiveData(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " begin " + getCurrentUser().getName() + " " + getCurrentUser().getAlias(),
			 "", "", 0);

		for (HighScore highScore : getCurrentUser().getHighScores()) {
			receiveData(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " score " + highScore.toString(), "", "", 0);
		}

		receiveData(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " einde", "", "", 0);
	}
}
