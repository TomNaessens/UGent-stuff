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

class ChooseGameButton extends JButton implements ActionListener, ChangeListener {

	GameLoungeModel gameLoungeModel;
	
	public ChooseGameButton(GameLoungeModel gameLoungeModel, String title) {
		super(title);
		
		this.gameLoungeModel = gameLoungeModel;
		
		gameLoungeModel.addChangeListener(this);
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.chooseGame();
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setEnabled(gameLoungeModel.isHosting());
	}
	
	

}
