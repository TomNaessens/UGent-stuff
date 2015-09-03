/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

import java.util.Collection;
import java.util.HashMap;
import javax.swing.JTabbedPane;
import lounge.misc.Model;
import network.NetworkAdapter;
import userManagement.Friend;
import userManagement.User;

public class ChatTabbedModel extends Model {

	boolean buttonEnabled;
	JTabbedPane chatPanes;
	HashMap<String, ChatPanel> teamIdChatMap;
	User user;

	public ChatTabbedModel(JTabbedPane chatPanes) {
		this.buttonEnabled = false;
		this.chatPanes = chatPanes;

		teamIdChatMap = new HashMap<String, ChatPanel>();
	}

	public void setButtonEnabled(boolean nietLeeg) {
		buttonEnabled = nietLeeg;
		fireStateChanged();
	}

	boolean getButtonEnabled() {
		return buttonEnabled;
	}

	public HashMap<String, ChatPanel> getTeamIdChatMap() {
		return teamIdChatMap;
	}

	public void sendTextToNetworkAdapter(String text) {

		String from = user.getAlias();


		for (Friend friend : ((ChatPanel) chatPanes.getSelectedComponent()).getModel().getChatters()) {
			if (!friend.getName().equals(user.getName())) {
				NetworkAdapter.getSingleton().sendChatMessage(from + " " + text, ((ChatPanel) chatPanes.getSelectedComponent()).getModel().getId(), friend.getIp().getHostAddress(), friend.getName());
			}
		}

		((ChatPanel) chatPanes.getSelectedComponent()).getModel().addText(from, text);
	}

	public void addChatMessage(String id, String van, String text) {
		if (teamIdChatMap.get(id) != null) {
			teamIdChatMap.get(id).getModel().addText(van, text);
		}
	}

	public void addChatter(String waar, Friend friend) {
		if (teamIdChatMap.get(waar) != null) {
			teamIdChatMap.get(waar).getModel().addChatter(friend);
		}
	}

	public void removeChatter(String waar, Friend friend) {
		teamIdChatMap.get(waar).getModel().removeChatter(friend);
	}

	public void editChatter(Friend friend) {
		for (ChatPanel chatPanel : teamIdChatMap.values()) {
			chatPanel.getModel().editChatter(friend);
		}
	}

	public void editChatter(Friend friend, String oldAlias, String newAlias) {
		for (ChatPanel chatPanel : teamIdChatMap.values()) {
			chatPanel.getModel().editChatter(friend, oldAlias, newAlias);
		}
	}

	public ChatPanel addChat(String id) {
		ChatModel chatModel = new ChatModel(id);
		ChatPanel chatPanel = new ChatPanel(chatModel);

		teamIdChatMap.put(id, chatPanel);

		return chatPanel;
	}

	public ChatPanel removeChat(String id) {
		return (teamIdChatMap.remove(id));
	}

	public User getUser() {
		return user;
	}

	public void setUser(User user) {
		this.user = user;
	}
}
