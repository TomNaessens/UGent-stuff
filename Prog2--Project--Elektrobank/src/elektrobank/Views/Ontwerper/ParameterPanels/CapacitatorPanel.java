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
import javax.swing.JTextField;

public class CapacitatorPanel extends JPanel {

	JTextField capaciteit;

	public CapacitatorPanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Capaciteit", new ParameterTextField(mBeheerder, 7), "F"));

	}
}
