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

public class PWDiodePanel extends JPanel {

	public PWDiodePanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Voorwaartse spanningsval", new ParameterTextField(mBeheerder, 8), "V"));

	}
}
