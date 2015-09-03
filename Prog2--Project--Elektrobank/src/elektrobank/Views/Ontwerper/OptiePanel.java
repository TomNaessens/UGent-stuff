/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Ontwerper;

import elektrobank.Models.ModelBeheerder;
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.GridLayout;
import javax.swing.GroupLayout;
import javax.swing.JPanel;

class OptiePanel extends JPanel {

	public OptiePanel(ModelBeheerder mBeheerder) {

		GroupLayout layout = new GroupLayout(this);
		setLayout(layout);

		JPanel controllerPanel = new SelectedActionPanel(mBeheerder);
		JPanel componentenPanel = new ComponentenPanel(mBeheerder.getSCModel(), mBeheerder.getPModel());
		JPanel parameterPanel = new ParameterPanel(mBeheerder.getPModel());

		layout.setVerticalGroup(
			   layout.createSequentialGroup()
				.addComponent(controllerPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE)
				.addComponent(componentenPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, 30)
				.addComponent(parameterPanel, GroupLayout.DEFAULT_SIZE, 200, 200)

		);

		layout.setHorizontalGroup(
			   layout.createParallelGroup()
				.addComponent(controllerPanel,GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(componentenPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(parameterPanel,GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
		);

	}
}
