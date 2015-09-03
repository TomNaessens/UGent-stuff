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

class GameNameLabel extends JLabel implements ChangeListener {

	GameLoungeModel gameLoungeModel;
	
	public GameNameLabel(GameLoungeModel gameLoungeModel, String gameName) {
		super(gameName);
		this.gameLoungeModel = gameLoungeModel; 
		
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setText(gameLoungeModel.getGameName());
	}

}
