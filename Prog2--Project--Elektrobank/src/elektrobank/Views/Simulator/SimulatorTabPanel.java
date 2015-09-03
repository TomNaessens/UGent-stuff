/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Simulator;

import elektrobank.Models.ModelBeheerder;
import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

public class SimulatorTabPanel extends JPanel {

	public SimulatorTabPanel(ModelBeheerder mBeheerder) {
		setLayout(new BorderLayout());

		SimulatorPanel simulatorPanel = new SimulatorPanel(mBeheerder.getSModel());
		JPanel simulatorOptiePanel = new SimulatorOptiePanel(mBeheerder);

		JScrollPane simulatorContainer = new JScrollPane(simulatorPanel);

		add(simulatorContainer,BorderLayout.CENTER);
		add(simulatorOptiePanel,BorderLayout.EAST);
	}

}
