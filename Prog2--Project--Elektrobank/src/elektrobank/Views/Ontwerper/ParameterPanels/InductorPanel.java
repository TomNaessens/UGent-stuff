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

public class InductorPanel extends JPanel {

	public InductorPanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Zelfinductie", new ParameterTextField(mBeheerder, 6), "H"));

	}
}
