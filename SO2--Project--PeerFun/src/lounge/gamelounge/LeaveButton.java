/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.gamelounge;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;

class LeaveButton extends JButton implements ActionListener {

	GameLoungeModel gameLoungeModel;
	
	public LeaveButton(GameLoungeModel gameLoungeModel, String title) {
		super(title);
		
		this.gameLoungeModel = gameLoungeModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.leaveGameLounge();
	}
	
	

}
