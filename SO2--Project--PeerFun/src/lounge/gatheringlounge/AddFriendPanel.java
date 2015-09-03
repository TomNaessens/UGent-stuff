/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.awt.GridLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import userManagement.Friend;

class AddFriendPanel extends JPanel {

	public AddFriendPanel(GatheringLoungeModel gatheringLoungeModel) {
		
		JLabel friendNameLabel = new JLabel("* Name friend:");
		JTextField friendNameField = new JTextField();
		
		JLabel friendIpLabel = new JLabel("* IP friend:");
		JTextField friendIpField = new JTextField();
			
		JButton addFriendButton = new AddFriendButton("Add", friendNameField, friendIpField, gatheringLoungeModel);
		
		GridLayout layout = new GridLayout(3,2);
		setLayout(layout);
	
		add(friendNameLabel);
		add(friendNameField);
		add(friendIpLabel);
		add(friendIpField);
		add(new JLabel());
		add(addFriendButton);
	}
	
	
	public AddFriendPanel(Friend friend, GatheringLoungeModel gatheringLoungeModel) {
		JLabel friendNameLabel = new JLabel("* Name friend:");
		JTextField friendNameField = new JTextField(friend.getName());
		
		JLabel friendIpLabel = new JLabel("* IP friend:");
		JTextField friendIpField = new JTextField(friend.getIp().getHostAddress());
		
		JButton addFriendButton = new AddFriendButton("Add", friendNameField, friendIpField, gatheringLoungeModel);
		
		GridLayout layout = new GridLayout(3, 2);
		setLayout(layout);
		
		add(friendNameLabel);
		add(friendNameField);
		add(friendIpLabel);
		add(friendIpField);
		add(new JLabel());
		add(addFriendButton);
	}
	
}
