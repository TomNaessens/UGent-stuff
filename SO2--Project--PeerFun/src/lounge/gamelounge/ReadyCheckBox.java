/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JCheckBox;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class ReadyCheckBox extends JCheckBox implements ActionListener, ChangeListener {

	GameLoungeModel gameLoungeModel;

	ReadyCheckBox(GameLoungeModel gameLoungeModel, String title) {
		super(title);

		this.gameLoungeModel = gameLoungeModel;

		addActionListener(this);
		gameLoungeModel.addChangeListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.switchReady();
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setEnabled(!gameLoungeModel.isHosting() && gameLoungeModel.getCurrentUser().getTeamId() != 0 && !gameLoungeModel.isReceivingFase());
		
		if(gameLoungeModel.isHosting()) {
			setSelected(true);
		}
	}
}
