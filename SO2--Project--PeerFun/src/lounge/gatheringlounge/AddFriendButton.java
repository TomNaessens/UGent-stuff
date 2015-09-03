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

class AddFriendButton extends JButton implements ActionListener {

	GatheringLoungeModel gatheringLoungeModel;
	JTextField friendNameField;
	JTextField friendIpField;
	
	public AddFriendButton(String title, JTextField friendNameField, JTextField friendIpField, GatheringLoungeModel gatheringLoungeModel) {
		super(title);
		
		this.gatheringLoungeModel = gatheringLoungeModel;
		this.friendNameField = friendNameField;
		this.friendIpField = friendIpField;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gatheringLoungeModel.addFriend(friendNameField.getText(), friendIpField.getText());
	}
	
}
