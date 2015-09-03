/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge;

import chat.Chat;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.JFrame;
import lounge.gamehub.GameHubModel;
import lounge.gamelounge.GameLoungeModel;
import lounge.gatheringlounge.GatheringLoungeModel;
import lounge.misc.Model;
import lounge.misc.UserModel;
import network.FileContents;
import network.NetworkAdapter;
import network.NetworkListener;
import userManagement.Friend;
import userManagement.FriendStatus;
import userManagement.HighScore;
import userManagement.Player;
import userManagement.User;

public abstract class AbstractLoungeModel extends Model implements NetworkListener {

	private JFrame window;
	private User currentUser;
	private UserModel userModel;
	public static final String NAME_CHANGE_TOKEN = "/nc";
	public static final String STATUS_CHANGE_TOKEN = "/tch";
	public static final String PRIVATE_CHAT_TOKEN = "/v";

	public AbstractLoungeModel(JFrame window, User currentUser) {
		this.window = window;
		this.currentUser = currentUser;

		userModel = new UserModel(this, currentUser);
	}

	@Override
	public void receiveData(String networkInput, String fromIp, String fromName, int port) {

		if (networkInput != null) {
			System.out.println("Tekst: " + networkInput + " From friend: " + fromName + " From IP: " + fromIp + " From port: " + port);

			if (networkInput.startsWith(NetworkAdapter.CHAT_TOKEN)) {
				String[] input = networkInput.split(" ");

				String naarId = input[1];
				String vanUser = input[2];

				String text = input[3];

				for (int i = 4; i < input.length; i++) {
					text += " " + input[i];
				}

				if (!(naarId.startsWith(GatheringLoungeModel.GATHERINGLOUNGE_NAME)
					 || naarId.startsWith(GameLoungeModel.GAMELOUNGE_NAME)
					 || naarId.startsWith(GameHubModel.GAMEHUB_NAME))) {

					if (naarId.equals(currentUser.getAlias()) && !vanUser.equals(getCurrentUser().getAlias())) {
						Chat.getSingleton().addChat(vanUser);
						try {
							Chat.getSingleton().addChatter(vanUser, new Friend(fromName, vanUser, InetAddress.getByName(fromIp)));
						} catch (UnknownHostException ex) {
							Logger.getLogger(AbstractLoungeModel.class.getName()).log(Level.SEVERE, null, ex);
						}
						Chat.getSingleton().addChatMessage(vanUser, vanUser, text);
					}

				} else if (naarId.equals(GameHubModel.GAMEHUB_NAME + ":")) {

					String[] invoer = networkInput.split(" ");
					int toTeam = Integer.parseInt(invoer[3]);
					String fromUser = invoer[4];

					String message = input[5];

					for (int i = 6; i < input.length; i++) {
						message += " " + input[i];
					}

					Chat.getSingleton().addChatMessage(GameHubModel.GAMEHUB_NAME + ": Team " + toTeam, fromUser, message);

				} else {

					Chat.getSingleton().addChatMessage(naarId, vanUser, text);

				}

			} else if (networkInput.startsWith(GameLoungeModel.STATUS_CHANGE_TOKEN)) {

				String[] input = networkInput.split(" ");
				String status = input[1];

				for (Friend friend : getCurrentUser().getFriends()) {
					if (friend.getName().equals(fromName)) {
						friend.setStatus(FriendStatus.valueOf(status));
					}
				}

				fireStateChanged();

			} else if (networkInput.startsWith("JOINED: ")) {

				Iterator<Friend> iterator = currentUser.getFriends().iterator();

				while (iterator.hasNext()) {
					Friend friend = iterator.next();

					if (friend.getName().equals(fromName)) {

						if (friend.getStatus() == FriendStatus.OFFLINE) {
							NetworkAdapter.getSingleton().sendMessage("JOINED: " + fromIp, fromIp, fromName);
							Chat.getSingleton().addChatter(GatheringLoungeModel.GATHERINGLOUNGE_NAME, friend);


							friend.setStatus(FriendStatus.IN_GATHERINGLOUNGE);

							fireStateChanged();
						}
					}
				}

			} else if (networkInput.startsWith("LEFT:")) {

				Iterator<Friend> iterator = currentUser.getFriends().iterator();
				while (iterator.hasNext()) {
					Friend friend = iterator.next();

					String ip = networkInput.split(" ")[1];

					if (friend.getName().equals(fromName)) {
						NetworkAdapter.getSingleton().closeConnection(ip, friend.getName());

						friend.setStatus(FriendStatus.OFFLINE);
						fireStateChanged();
					}
				}

			} else if (networkInput.startsWith(GatheringLoungeModel.REQUEST_PROFILE_TOKEN)) {

				NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " begin " + getCurrentUser().getName() + " " + getCurrentUser().getAlias(),
					 fromIp, port);
				
				for (HighScore highScore : getCurrentUser().getHighScores()) {
					NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " score " + highScore.toString(), fromIp, port);
				}

				NetworkAdapter.getSingleton().sendMessage(GatheringLoungeModel.RECEIVE_PROFILE_TOKEN + " einde", fromIp, port);
			}
		}

	}

	@Override
	public void receiveFileContents(FileContents file) {
	}
	
	@Override
	public void sendData(String message, String ip, int port) {
	}

	public User getCurrentUser() {
		return currentUser;
	}

	public void setCurrentUser(User currentUser) {
		this.currentUser = currentUser;
	}

	public abstract ArrayList<Friend> getFriends();

	public abstract ArrayList<Player> getPlayers();

	public void windowClosed() {
	
	}
	
	public UserModel getUserModel() {
		return userModel;
	}

	public JFrame getWindow() {
		return window;
	}

}
