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

class ChangeNameListener {

	ChangeNameListener(GameLoungeModel gameLoungeModel, JLabel gameName) {
		gameName.setText(gameLoungeModel.getGameName());
	}

}
