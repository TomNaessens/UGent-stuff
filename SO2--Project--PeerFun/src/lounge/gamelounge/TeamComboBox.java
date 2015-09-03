/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import javax.swing.JComboBox;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class TeamComboBox extends JComboBox implements ChangeListener, ItemListener {

	GameLoungeModel gameLoungeModel;

	public TeamComboBox(GameLoungeModel gameLoungeModel) {
		this.gameLoungeModel = gameLoungeModel;

		gameLoungeModel.addChangeListener(this);
		addItemListener(this);
	}

	public void fillBox() {
		
		removeItemListener(this);
		
		removeAllItems();
		addItem("?");

		for (int i = 1; i <= gameLoungeModel.getGameTeams(); i++) {
			addItem("Team " + i);
		}
		
		setSelectedIndex(gameLoungeModel.getCurrentUser().getTeamId());
		
		addItemListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		fillBox();
		setEnabled(!gameLoungeModel.isReceivingFase());
	}

	@Override
	public void itemStateChanged(ItemEvent ie) {
		if (getSelectedItem() != null && ie.getStateChange() == 1) {
			String result = (String) getSelectedItem();
			if(result.equals("?")) {
				gameLoungeModel.setTeam(0);
			} else {
				gameLoungeModel.setTeam(Integer.parseInt(result.split(" ")[1]));
			}
		}
	}
}
