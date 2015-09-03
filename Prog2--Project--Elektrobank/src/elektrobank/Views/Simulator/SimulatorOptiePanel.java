/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Simulator;

import elektrobank.Controllers.Buttons.LoopToggleButton;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Simulator.SimulatorModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JFormattedTextField;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSpinner;
import javax.swing.JToggleButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class SimulatorOptiePanel extends JPanel {

	private static SimulatorModel sModel;

	public SimulatorOptiePanel(final ModelBeheerder mBeheerder) {

		GroupLayout layout = new GroupLayout(this);
		setLayout(layout);
		layout.setAutoCreateContainerGaps(true);

		sModel = mBeheerder.getSModel();

		JButton stapButton = new JButton("Stap simulatie");
		stapButton.addActionListener(new ActionListener() {

			public void actionPerformed(ActionEvent e) {
				sModel.doStep();
			}
		});

		final JToggleButton loopButton = new LoopToggleButton(sModel, "Loop simulatie");

		JLabel snelheidLabel = new JLabel("Snelheid:");
		final JSpinner snelheidSpinner = new JSpinner(mBeheerder.getSSHModel());
		((JSpinner.DefaultEditor) snelheidSpinner.getEditor()).getTextField().setHorizontalAlignment(JFormattedTextField.RIGHT);
		snelheidSpinner.addChangeListener(new ChangeListener() {

			public void stateChanged(ChangeEvent e) {
				sModel.getTimer().setDelay(Integer.parseInt(snelheidSpinner.getValue().toString()));
			}
		});

		JLabel tijdstapLabel = new JLabel("Tijdstap:");
		JSpinner tijdstapSpinner = new JSpinner(mBeheerder.getSTSModel());
		((JSpinner.DefaultEditor) tijdstapSpinner.getEditor()).getTextField().setHorizontalAlignment(JFormattedTextField.RIGHT);

		JButton resetButton = new JButton("Reset simulatie");
		resetButton.addActionListener(new ActionListener() {

			public void actionPerformed(ActionEvent e) {
				sModel.resetSim();
			}
		});


		layout.setHorizontalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.CENTER)
				.addComponent(stapButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(loopButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addGroup(layout.createSequentialGroup()
					.addComponent(snelheidLabel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addComponent(snelheidSpinner, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				)
				.addGroup(layout.createSequentialGroup()
					.addComponent(tijdstapLabel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addComponent(tijdstapSpinner, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				)
				.addComponent(resetButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
		);

		layout.setVerticalGroup(
			   layout.createSequentialGroup()
					.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addComponent(stapButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addComponent(loopButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
						.addComponent(snelheidLabel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
						.addComponent(snelheidSpinner, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					)
					.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
						.addComponent(tijdstapLabel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
						.addComponent(tijdstapSpinner, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					)
					.addComponent(resetButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
					.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE));

	}
}
