/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.gamelounge;

import chat.ChatTabbedPanel;
import java.awt.Dimension;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import lounge.misc.EditProfileAction;

public class GameLoungePanel extends JPanel {

	ReadyCheckBox readyCheckBox;
	StartButton startButton;
	GameLoungeModel gameLoungeModel;
	GroupLayout layout;
	
	public GameLoungePanel(GameLoungeModel gameLoungeModel) {
		
		this.gameLoungeModel = gameLoungeModel;
		readyCheckBox = new ReadyCheckBox(gameLoungeModel, "I'm ready!");
		readyCheckBox.setSelected(gameLoungeModel.isHosting());
		readyCheckBox.setEnabled(!gameLoungeModel.isHosting());
		
		startButton = new StartButton(gameLoungeModel, "Start game");
				
		JButton editButton = new JButton("Edit profile");
		editButton.setAction(new EditProfileAction(gameLoungeModel.getCurrentUser(), gameLoungeModel.getUserModel()));
		
		JButton leaveButton = new LeaveButton(gameLoungeModel, "Leave GameLounge");
		JLabel playersReady = new ReadyLabel(gameLoungeModel);
		
		
		KickButton kickButton = new KickButton(gameLoungeModel, "Kick player(s)");
		kickButton.setEnabled(gameLoungeModel.isHosting());
		
		JButton inviteButton = new OpenInviteButton(gameLoungeModel, "Invite player...");
		
		ChatTabbedPanel chatPanel = gameLoungeModel.getChatPanel();
		
		JPanel gameInfoPanel = new GameInfoPanel(gameLoungeModel);
		
		TeamComboBox teamComboBox = new TeamComboBox(gameLoungeModel);
		teamComboBox.fillBox();
		
		JList friendList = gameLoungeModel.getFriendJList();
		
		JScrollPane friendScrollPane = new JScrollPane(friendList);
		friendScrollPane.setPreferredSize(new Dimension(250, 40));
		
		layout = new GroupLayout(this);
		
		layout.setAutoCreateContainerGaps(true);
		
		layout.setVerticalGroup(
			   layout.createSequentialGroup()
			   	.addGroup(layout.createParallelGroup()
					.addComponent(chatPanel)
					.addGroup(layout.createSequentialGroup()
						.addComponent(gameInfoPanel)
						.addComponent(teamComboBox, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, 15)
						.addComponent(friendScrollPane)
					)
			 
				)	
				.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
					.addComponent(startButton)
			 
					.addComponent(editButton)
					.addComponent(leaveButton)
			 
			 
					.addComponent(playersReady)
					.addComponent(readyCheckBox)
			
					.addComponent(kickButton)
					.addComponent(inviteButton)
				)
		);

		layout.setHorizontalGroup(
			   layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addComponent(chatPanel)
						.addGroup(layout.createSequentialGroup()
							.addComponent(startButton)
			 
							.addComponent(editButton)
							.addComponent(leaveButton)
			 
							.addComponent(playersReady)
							.addComponent(readyCheckBox)
						)
					)	
					.addGroup(layout.createParallelGroup()
						.addGroup(layout.createParallelGroup()
							.addComponent(gameInfoPanel)
							.addComponent(teamComboBox)
							.addComponent(friendScrollPane)
						)
						.addGroup(layout.createSequentialGroup()
							.addComponent(kickButton)
							.addComponent(inviteButton)
						)
					)
		);
			
		setLayout(layout);
	
	}
	
}
