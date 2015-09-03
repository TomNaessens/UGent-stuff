/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import userManagement.FriendStatus;
import userManagement.Player;

public class StartButton extends JButton implements ActionListener, ChangeListener {

	GameLoungeModel gameLoungeModel;

	public StartButton(GameLoungeModel gameLoungeModel, String title) {
		super(title);

		this.gameLoungeModel = gameLoungeModel;

		addActionListener(this);
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.startGame();
	}

	@Override
	public void stateChanged(ChangeEvent ce) {

		if (gameLoungeModel.getGameTeams() != 0) {
			boolean enabled = true;

			if (gameLoungeModel.getAmountReady() != gameLoungeModel.getGamePlayers()) {
				enabled = false;
			}

			int[] teams = new int[gameLoungeModel.getGameTeams()];
			int playersPerTeam = gameLoungeModel.getGamePlayers() / gameLoungeModel.getGameTeams();

			for (Player player : gameLoungeModel.getPlayers()) {
				if (player.getStatus() == FriendStatus.READY && player.getTeamId() != 0) {
					teams[player.getTeamId() - 1]++;
				}
			}

			if (gameLoungeModel.getCurrentUser().getTeamId() == 0) {
				enabled = false;
			} else {
				teams[gameLoungeModel.getCurrentUser().getTeamId() - 1]++;
			}

			for (int i = 0; i < teams.length; i++) {
				if (teams[i] != playersPerTeam) {
					enabled = false;
				}
			}

			setEnabled(gameLoungeModel.isHosting() && enabled);

		} else {

			setEnabled(false);
		}
	}
}
