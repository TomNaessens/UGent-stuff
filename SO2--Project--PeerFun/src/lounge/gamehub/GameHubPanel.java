/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamehub;

import chat.Chat;
import chat.ChatTabbedPanel;
import javax.swing.GroupLayout;
import javax.swing.JPanel;
import userManagement.Player;
import userManagement.User;

public class GameHubPanel extends JPanel {

	public GameHubPanel(GameHubModel gameHubModel) {

		ChatTabbedPanel chatTabbedPanel = gameHubModel.getChatTabbedPanel();

		JPanel gameGui = gameHubModel.getGameGui();

		GroupLayout layout = new GroupLayout(this);
		
		layout.setHorizontalGroup(
			 layout.createSequentialGroup()
				.addComponent(gameGui)
				.addComponent(chatTabbedPanel)
		);

		layout.setVerticalGroup(
			 layout.createParallelGroup()
				.addComponent(gameGui)
				.addComponent(chatTabbedPanel)
		);
		
		setLayout(layout);
	}
}
