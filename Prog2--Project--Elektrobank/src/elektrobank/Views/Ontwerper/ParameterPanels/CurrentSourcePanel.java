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

public class CurrentSourcePanel extends JPanel {

	public CurrentSourcePanel(ModelBeheerder mBeheerder) {
		add(new SingleParameterPanel("Stroom", new ParameterTextField(mBeheerder, 9), "A"));

	}
}
