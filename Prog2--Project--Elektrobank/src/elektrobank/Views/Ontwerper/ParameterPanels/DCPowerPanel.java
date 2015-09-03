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
import javax.swing.JPanel;

public class DCPowerPanel extends JPanel {

	public DCPowerPanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Voltage", new ParameterTextField(mBeheerder, 0), "V"));
	}
}
