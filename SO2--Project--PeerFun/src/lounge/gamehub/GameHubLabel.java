/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamehub;

import javax.swing.JLabel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import userManagement.FriendStatus;
import userManagement.Player;

public class GameHubLabel extends JLabel implements ChangeListener {

	GameHubModel gameHubModel;
	Player player;

	public GameHubLabel(GameHubModel gameHubModel, Player player) {
		this.gameHubModel = gameHubModel;
		this.player = player;
		
		if (player.isIsReady() || player.getStatus() == FriendStatus.IS_HOSTING) {
			setText("I'm ready!");
		} else {
			setText("Still receiving the game...");
		}

		gameHubModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {

		if (player.isIsReady()) {
			setText("I'm ready!");
		} else {
			setText("Still receiving the game...");
		}

	}
}
