/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JTextField;
import userManagement.Friend;

class EditFriendButton extends JButton implements ActionListener {

	Friend friend;
	JTextField friendIpField;
	GatheringLoungeModel gatheringLoungeModel;
	
	public EditFriendButton(String title, Friend friend, JTextField friendIpField, GatheringLoungeModel gatheringLoungeModel) {
		super(title);
		
		this.friend = friend;
		this.gatheringLoungeModel = gatheringLoungeModel;
		this.friendIpField = friendIpField;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gatheringLoungeModel.editFriend(friend, friendIpField.getText());
	}
	
}
