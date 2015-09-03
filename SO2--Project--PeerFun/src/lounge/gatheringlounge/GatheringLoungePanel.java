/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import chat.ChatTabbedPanel;
import java.awt.Dimension;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.LayoutStyle;
import lounge.misc.EditProfileAction;

public class GatheringLoungePanel extends JPanel {

	GatheringLoungeModel gatheringLoungeModel;
	
	public GatheringLoungePanel(GatheringLoungeModel gatheringLoungeModel) {
		this.gatheringLoungeModel = gatheringLoungeModel;
		
		JButton hostButton = new HostButton("Host", gatheringLoungeModel);
		JButton editButton = new JButton();
		JButton viewProfileButton = new ViewProfileButton("View profile", gatheringLoungeModel);
		
		JButton addFriendButton = new OpenAddFriendFrameButton("Add", gatheringLoungeModel);
		JButton viewFriendButton = new ViewFriendButton("View", gatheringLoungeModel);
		JButton editFriendButton = new OpenEditFriendFrameButton("Edit", gatheringLoungeModel);
		JButton deleteFriendButton = new DeleteFriendButton("Delete", gatheringLoungeModel);
		
		JLabel portLabel = new JLabel("Username: "+ gatheringLoungeModel.getCurrentUser().getName() + ", Uw poort: "+ Integer.toString(gatheringLoungeModel.getHostPort()));
		
		ChatTabbedPanel chatTabbedPanel = gatheringLoungeModel.getChatPanel();
		
		editButton.setAction(new EditProfileAction(gatheringLoungeModel.getCurrentUser(), gatheringLoungeModel.getUserModel()));
		
		JList friendList = gatheringLoungeModel.getFriendJList();
		
		JScrollPane friendScrollPane = new JScrollPane(friendList);
		friendScrollPane.setPreferredSize(new Dimension(250, 40));
		
		GroupLayout layout = new GroupLayout(this);

		layout.setAutoCreateContainerGaps(true);
		
		layout.setVerticalGroup(
			   layout.createSequentialGroup()
			   	.addGroup(layout.createParallelGroup()
					.addComponent(chatTabbedPanel)
					.addComponent(friendScrollPane)
				)	
				.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
					.addComponent(hostButton)
					.addComponent(editButton)
					.addComponent(viewProfileButton)
					.addComponent(portLabel)
					.addComponent(addFriendButton)
					.addComponent(editFriendButton)
					.addComponent(viewFriendButton)
					.addComponent(deleteFriendButton)
				)
		);

		layout.setHorizontalGroup(
			   layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addComponent(chatTabbedPanel)
						.addGroup(layout.createSequentialGroup()
							.addComponent(hostButton)
							.addComponent(editButton)   
							.addComponent(viewProfileButton)     
							.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
							.addComponent(portLabel)			
						)
					)	
					.addGroup(layout.createParallelGroup()
						.addComponent(friendScrollPane)
						.addGroup(layout.createSequentialGroup()
							.addComponent(addFriendButton)
							.addComponent(editFriendButton)
							.addComponent(viewFriendButton)
							.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
							.addComponent(deleteFriendButton)
						)
					)
		);

		setLayout(layout);
	}
	
	
}
