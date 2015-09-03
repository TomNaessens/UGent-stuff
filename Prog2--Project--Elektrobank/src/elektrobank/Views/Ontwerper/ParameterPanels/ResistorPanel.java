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

public class ResistorPanel extends JPanel {

	public ResistorPanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Weerstand", new ParameterTextField(mBeheerder, 5), "Ohm"));
	}
}
