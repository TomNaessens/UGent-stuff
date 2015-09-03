/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

import javax.swing.GroupLayout;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import lounge.gamehub.GameHubModel;
import lounge.gamelounge.GameLoungeModel;
import lounge.gatheringlounge.GatheringLoungeModel;
import userManagement.Friend;

public class ChatTabbedPanel extends JPanel {

	JTabbedPane chatPanes;
	ChatTabbedModel chatTabbedModel;

	public ChatTabbedPanel() {
		chatPanes = new JTabbedPane();
		chatPanes.setTabPlacement(JTabbedPane.TOP);

		chatTabbedModel = new ChatTabbedModel(chatPanes);

		ChatMessageField chatTextField = new ChatMessageField(chatTabbedModel);
		ChatButton chatButton = new ChatButton(chatTabbedModel, chatTextField);

		GroupLayout layout = new GroupLayout(this);

		layout.setHorizontalGroup(
			 layout.createParallelGroup().addComponent(chatPanes).addGroup(layout.createSequentialGroup().addComponent(chatTextField).addComponent(chatButton)));

		layout.setVerticalGroup(
			 layout.createSequentialGroup().addComponent(chatPanes).addGroup(layout.createParallelGroup().addComponent(chatTextField).addComponent(chatButton)));

		setLayout(layout);
	}

	public void addChat(String title) {
		if (getChatTabbedModel().getTeamIdChatMap().get(title) == null && !title.equals(getChatTabbedModel().getUser().getAlias())) {

			ChatPanel chatPanel = chatTabbedModel.addChat(title);

			boolean enabled = !(title.startsWith(GatheringLoungeModel.GATHERINGLOUNGE_NAME)
				 || title.startsWith(GameLoungeModel.GAMELOUNGE_NAME)
				 || title.startsWith(GameHubModel.GAMEHUB_NAME));

			chatPanes.addTab(title, chatPanel);
			chatPanes.setTabComponentAt(chatPanes.indexOfTab(title), new CloseTab(this, title, enabled));
			chatPanes.setSelectedIndex(chatPanes.indexOfTab(title));
			chatPanel.getModel().addChatter(chatTabbedModel.getUser());
		}
	}

	public void addChatter(String id, Friend friend) {
		chatTabbedModel.addChatter(id, friend);
	}

	public void addChatMessage(String id, String van, String text) {
		chatTabbedModel.addChatMessage(id, van, text);
	}

	public void removeChatter(String id, Friend friend) {
		chatTabbedModel.removeChatter(id, friend);
	}

	public void removeChat(String id) {
		chatPanes.remove(chatTabbedModel.removeChat(id));
	}

	public ChatTabbedModel getChatTabbedModel() {
		return chatTabbedModel;
	}

	public JTabbedPane getChatPanes() {
		return chatPanes;
	}
}