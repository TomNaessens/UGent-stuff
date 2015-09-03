/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import javax.swing.JTextArea;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class GameDescriptionArea extends JTextArea implements ChangeListener {

	GameLoungeModel gameLoungeModel;

	public GameDescriptionArea(GameLoungeModel gameLoungeModel, String gameDescription) {
		super(gameDescription, 1, 15);
		this.gameLoungeModel = gameLoungeModel;

		setEditable(false);
		setLineWrap(true);
		
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setText(gameLoungeModel.getGameDescription());
	}
}
