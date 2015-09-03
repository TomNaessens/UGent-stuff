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
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class OpenInviteButton extends JButton implements ChangeListener, ActionListener {

	GameLoungeModel gameLoungeModel;
	
	public OpenInviteButton(GameLoungeModel gameLoungeModel, String title) {
		super(title);
		
		this.gameLoungeModel = gameLoungeModel;
		
		addActionListener(this);
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setEnabled(gameLoungeModel.isHosting());
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.openInviteFrame();
	}
	


}
