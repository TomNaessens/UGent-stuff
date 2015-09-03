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

public class StartTimer implements ActionListener {

	GameLoungeModel gameLoungeModel;
	
	public StartTimer(GameLoungeModel gameLoungeModel) {
		this.gameLoungeModel = gameLoungeModel;
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.tick();
	}

}
