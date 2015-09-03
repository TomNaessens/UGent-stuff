/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Ontwerper.ParameterPanels;

import elektrobank.Controllers.ParameterTextField;
import elektrobank.Models.ModelBeheerder;
import java.awt.Dimension;
import java.awt.GridLayout;
import javax.swing.JPanel;

public class ACPowerPanel extends JPanel {

	public ACPowerPanel(ModelBeheerder mBeheerder) {

		setPreferredSize(new Dimension(200,200));

		GridLayout layout = new GridLayout(4, 1, 0, 0);
		setLayout(layout);

		add(new SingleParameterPanel("Amplitude", new ParameterTextField(mBeheerder, 1), "V"));
		add(new SingleParameterPanel("Offset", new ParameterTextField(mBeheerder, 2), "V"));
		add(new SingleParameterPanel("Frequentie", new ParameterTextField(mBeheerder, 3), "Hz"));
		add(new SingleParameterPanel("Fase", new ParameterTextField(mBeheerder, 4), "r"));
	}
}
