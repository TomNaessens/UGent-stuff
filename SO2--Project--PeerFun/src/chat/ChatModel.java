/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import lounge.misc.Model;
import userManagement.Friend;

public class ChatModel extends Model {

	private String id;
	private String from;
	private String text;
	private String at;
	private int messageId;
	private ArrayList<Friend> chatters;

	public ChatModel(String id) {
		this.id = id;
		chatters = new ArrayList<Friend>();
		messageId = 0;
	}

	public String getId() {
		return id;
	}

	public void addText(String from, String text) {
		this.from = from;
		this.text = text;

		DateFormat dateFormat = new SimpleDateFormat("HH:mm");
		Date date = new Date();
		at = dateFormat.format(date);

		messageId++;

		fireStateChanged();
	}

	public void addChatter(Friend friend) {

		boolean exists = false;

		for (Friend current : chatters) {
			if (current.getName().equals(friend.getName())) {
				exists = true;
			}
		}

		if (!exists) {
			if (!friend.getName().equals(Chat.getSingleton().getChatTabbedModel().getUser().getName())) {
				addText("GameInfo", friend.getAlias() + " has joined the chatroom.");
			}
			chatters.add(friend);

			Collections.sort(chatters, new CompareByAlias());

			fireStateChanged();
		}
	}

	public void removeChatter(Friend friend) {

		if (!friend.getName().equals(Chat.getSingleton().getChatTabbedModel().getUser().getName())) {
			addText("GameInfo", friend.getAlias() + " has left the chatroom.");
		}
		chatters.remove(friend);

		fireStateChanged();
	}

	public void editChatter(Friend friend) {
		for (Friend friends : chatters) {
			if(friends.getName().equals(friend.getName())) {
				addText("GameInfo", "You are now known as " + friend.getAlias());
				friends.setAlias(friend.getAlias());
			}
		}
		
		fireStateChanged();
	}
	
	public void editChatter(Friend friend, String oldAlias, String newAlias) {
		for (Friend friends : chatters) {
			if(friends.getName().equals(friend.getName())) {
				addText("GameInfo", oldAlias + " changed his nickname to " + newAlias);
				friends.setAlias(friend.getAlias());
			}
		}
		
		fireStateChanged();
	}
	
	public String getText() {
		return text;
	}

	public String getFrom() {
		return from;
	}

	public String getAt() {
		return at;
	}

	public int getMessageId() {
		return messageId;
	}

	public ArrayList<Friend> getChatters() {
		return chatters;
	}

	public JList getChatJList() {
		DefaultListModel chatListModel = new DefaultListModel();

		ChatList chatList;

		chatList = new ChatList(this, chatListModel);
		chatList.setCellRenderer(new ChatListRenderer());

		fireStateChanged();

		return chatList;
	}
}
