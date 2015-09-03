/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Menu;

import elektrobank.Models.Simulator.SimulatorModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class MenuLoopButton extends JCheckBoxMenuItem implements ActionListener, ChangeListener {

	private SimulatorModel sModel;

	public MenuLoopButton(SimulatorModel sModel, String title) {
		super(title);

		this.sModel = sModel;

		addActionListener(this);

		sModel.addChangeListener(this);
	}

	public void stateChanged(ChangeEvent e) {
		setSelected(sModel.getTimer().isRunning());
	}

	public void actionPerformed(ActionEvent e) {
		sModel.changeTimer();
	}
}
