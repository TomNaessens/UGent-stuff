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

public class KickButton extends JButton implements ActionListener, ChangeListener {

	GameLoungeModel gameLoungeModel;
	
	public KickButton(GameLoungeModel gameLoungeModel, String title) {
		super(title);
		
		this.gameLoungeModel = gameLoungeModel;
		
		addActionListener(this);
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.kickPlayers();
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setEnabled(gameLoungeModel.isHosting());
	}

}
