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

class GamePlayersLabel extends JLabel implements ChangeListener {

	GameLoungeModel gameLoungeModel;
	
	public GamePlayersLabel(GameLoungeModel gameLoungeModel, String gamePlayers) {
		super(gamePlayers);
		this.gameLoungeModel = gameLoungeModel; 
		
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setText(Integer.toString(gameLoungeModel.getGamePlayers()));
	}

}
