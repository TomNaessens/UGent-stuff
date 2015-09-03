/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.gamelounge;

import javax.swing.JLabel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class ReadyLabel extends JLabel implements ChangeListener {

	GameLoungeModel gameLoungeModel;
	
	public ReadyLabel(GameLoungeModel gameLoungeModel) {
		this.gameLoungeModel = gameLoungeModel;
		
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		this.setText("# players ready: " + gameLoungeModel.getAmountReady());
	}

}
