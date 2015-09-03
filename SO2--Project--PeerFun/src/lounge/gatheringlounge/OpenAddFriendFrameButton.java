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

class OpenAddFriendFrameButton extends JButton implements ActionListener {

	GatheringLoungeModel gatheringLoungeModel;
	
	public OpenAddFriendFrameButton(String string, GatheringLoungeModel gatheringLoungeModel) {
		super(string);
		
		this.gatheringLoungeModel = gatheringLoungeModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gatheringLoungeModel.openAddFriendFrame();
	}
	
}
