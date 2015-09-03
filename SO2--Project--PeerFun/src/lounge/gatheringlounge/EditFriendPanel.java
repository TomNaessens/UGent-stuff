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

class EditFriendPanel extends JPanel {

	public EditFriendPanel(Friend friend, GatheringLoungeModel gatheringLoungeModel) {

		JLabel friendIpLabel = new JLabel("* IP friend:");
		JTextField friendIpField = new JTextField(friend.getIp().getHostAddress());

		JButton editFriendButton = new EditFriendButton("Edit", friend, friendIpField, gatheringLoungeModel);

		GridLayout layout = new GridLayout(2, 2);
		setLayout(layout);

		add(friendIpLabel);
		add(friendIpField);
		add(new JLabel());
		add(editFriendButton);
	}
}
