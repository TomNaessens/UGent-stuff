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

class ViewFriendButton extends JButton implements ActionListener {

	GatheringLoungeModel gatheringLoungeModel;
	
	public ViewFriendButton(String view_friend, GatheringLoungeModel gatheringLoungeModel) {
		super(view_friend);
		
		this.gatheringLoungeModel = gatheringLoungeModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		gatheringLoungeModel.requestProfile();
	}

}
