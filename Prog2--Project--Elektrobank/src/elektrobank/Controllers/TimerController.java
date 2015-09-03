/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers;

import elektrobank.Models.Simulator.SimulatorModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class TimerController implements ActionListener {

	SimulatorModel sModel;

	public TimerController(SimulatorModel sModel) {
		this.sModel = sModel;
	}

	public void actionPerformed(ActionEvent e) {
		sModel.doStep();
	}
}
